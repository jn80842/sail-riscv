import LeanRV64DLEAN.Main

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 10_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail

namespace LeanRV64DLEAN.Functions

open zicondop
open wxfunct6
open wvxfunct6
open wvvfunct6
open wvfunct6
open write_kind
open word_width
open wmvxfunct6
open wmvvfunct6
open vxsgfunct6
open vxmsfunct6
open vxmfunct6
open vxmcfunct6
open vxfunct6
open vxcmpfunct6
open vvmsfunct6
open vvmfunct6
open vvmcfunct6
open vvfunct6
open vvcmpfunct6
open vregno
open vregidx
open vmlsop
open vlewidth
open visgfunct6
open virtaddr
open vimsfunct6
open vimfunct6
open vimcfunct6
open vifunct6
open vicmpfunct6
open vfwunary0
open vfunary1
open vfunary0
open vfnunary0
open vext8funct6
open vext4funct6
open vext2funct6
open uop
open sopw
open sop
open seed_opst
open rounding_mode
open ropw
open rop
open rmvvfunct6
open rivvfunct6
open rfvvfunct6
open regno
open regidx
open read_kind
open pmpMatch
open pmpAddrMatch
open physaddr
open option
open nxsfunct6
open nxfunct6
open nvsfunct6
open nvfunct6
open nisfunct6
open nifunct6
open mvxmafunct6
open mvxfunct6
open mvvmafunct6
open mvvfunct6
open mmfunct6
open maskfunct3
open iop
open fwvvmafunct6
open fwvvfunct6
open fwvfunct6
open fwvfmafunct6
open fwvffunct6
open fwffunct6
open fvvmfunct6
open fvvmafunct6
open fvvfunct6
open fvfmfunct6
open fvfmafunct6
open fvffunct6
open f_un_x_op_H
open f_un_x_op_D
open f_un_rm_xf_op_S
open f_un_rm_xf_op_H
open f_un_rm_xf_op_D
open f_un_rm_fx_op_S
open f_un_rm_fx_op_H
open f_un_rm_fx_op_D
open f_un_rm_ff_op_S
open f_un_rm_ff_op_H
open f_un_rm_ff_op_D
open f_un_op_x_S
open f_un_op_f_S
open f_un_f_op_H
open f_un_f_op_D
open f_madd_op_S
open f_madd_op_H
open f_madd_op_D
open f_bin_x_op_H
open f_bin_x_op_D
open f_bin_rm_op_S
open f_bin_rm_op_H
open f_bin_rm_op_D
open f_bin_op_x_S
open f_bin_op_f_S
open f_bin_f_op_H
open f_bin_f_op_D
open extop_zbb
open extension
open exception
open ctl_result
open csrop
open cregidx
open cbop_zicbom
open bropw_zbb
open bropw_zba
open brop_zbs
open brop_zbkb
open brop_zbb
open brop_zba
open bop
open biop_zbs
open barrier_kind
open ast
open amoop
open agtype
open TrapVectorMode
open TR_Result
open SATPMode
open Retired
open Register
open Privilege
open PmpAddrMatchType
open PTW_Result
open PTW_Error
open PTE_Check
open InterruptType
open FetchResult
open Ext_PhysAddr_Check
open Ext_FetchAddr_Check
open Ext_DataAddr_Check
open Ext_ControlAddr_Check
open ExtStatus
open ExceptionType
open Architecture
open AccessType

def initialize_registers (_ : Unit) : SailM Unit := do
  dbg_trace "initialize_registers 1"
  writeReg PC (← (undefined_bitvector ((2 ^i 3) *i 8)))
  dbg_trace "initialize_registers 2"
  writeReg nextPC (← (undefined_bitvector ((2 ^i 3) *i 8)))
  dbg_trace "initialize_registers "
  writeReg instbits (← (undefined_bitvector ((2 ^i 3) *i 8)))
  dbg_trace "initialize_registers "
  writeReg x1 (← (undefined_bitvector ((2 ^i 3) *i 8)))
  dbg_trace "initialize_registers "
  writeReg x2 (← (undefined_bitvector ((2 ^i 3) *i 8)))
  dbg_trace "initialize_registers "
  writeReg x3 (← (undefined_bitvector ((2 ^i 3) *i 8)))
  dbg_trace "initialize_registers "
  writeReg x4 (← (undefined_bitvector ((2 ^i 3) *i 8)))
  dbg_trace "initialize_registers "
  writeReg x5 (← (undefined_bitvector ((2 ^i 3) *i 8)))
  dbg_trace "initialize_registers "
  writeReg x6 (← (undefined_bitvector ((2 ^i 3) *i 8)))
  dbg_trace "initialize_registers "
  writeReg x7 (← (undefined_bitvector ((2 ^i 3) *i 8)))
  dbg_trace "initialize_registers "
  writeReg x8 (← (undefined_bitvector ((2 ^i 3) *i 8)))
  dbg_trace "initialize_registers "
  writeReg x9 (← (undefined_bitvector ((2 ^i 3) *i 8)))
  dbg_trace "initialize_registers "
  writeReg x10 (← (undefined_bitvector ((2 ^i 3) *i 8)))
  dbg_trace "initialize_registers "
  writeReg x11 (← (undefined_bitvector ((2 ^i 3) *i 8)))
  dbg_trace "initialize_registers "
  writeReg x12 (← (undefined_bitvector ((2 ^i 3) *i 8)))
  dbg_trace "initialize_registers "
  writeReg x13 (← (undefined_bitvector ((2 ^i 3) *i 8)))
  dbg_trace "initialize_registers "
  writeReg x14 (← (undefined_bitvector ((2 ^i 3) *i 8)))
  dbg_trace "initialize_registers "
  writeReg x15 (← (undefined_bitvector ((2 ^i 3) *i 8)))
  dbg_trace "initialize_registers "
  writeReg x16 (← (undefined_bitvector ((2 ^i 3) *i 8)))
  dbg_trace "initialize_registers "
  writeReg x17 (← (undefined_bitvector ((2 ^i 3) *i 8)))
  dbg_trace "initialize_registers "
  writeReg x18 (← (undefined_bitvector ((2 ^i 3) *i 8)))
  dbg_trace "initialize_registers "
  writeReg x19 (← (undefined_bitvector ((2 ^i 3) *i 8)))
  dbg_trace "initialize_registers "
  writeReg x20 (← (undefined_bitvector ((2 ^i 3) *i 8)))
  dbg_trace "initialize_registers "
  writeReg x21 (← (undefined_bitvector ((2 ^i 3) *i 8)))
  dbg_trace "initialize_registers "
  writeReg x22 (← (undefined_bitvector ((2 ^i 3) *i 8)))
  dbg_trace "initialize_registers "
  writeReg x23 (← (undefined_bitvector ((2 ^i 3) *i 8)))
  dbg_trace "initialize_registers "
  writeReg x24 (← (undefined_bitvector ((2 ^i 3) *i 8)))
  dbg_trace "initialize_registers "
  writeReg x25 (← (undefined_bitvector ((2 ^i 3) *i 8)))
  dbg_trace "initialize_registers "
  writeReg x26 (← (undefined_bitvector ((2 ^i 3) *i 8)))
  dbg_trace "initialize_registers "
  writeReg x27 (← (undefined_bitvector ((2 ^i 3) *i 8)))
  dbg_trace "initialize_registers "
  writeReg x28 (← (undefined_bitvector ((2 ^i 3) *i 8)))
  dbg_trace "initialize_registers "
  writeReg x29 (← (undefined_bitvector ((2 ^i 3) *i 8)))
  dbg_trace "initialize_registers "
  writeReg x30 (← (undefined_bitvector ((2 ^i 3) *i 8)))
  dbg_trace "initialize_registers "
  writeReg x31 (← (undefined_bitvector ((2 ^i 3) *i 8)))
  dbg_trace "initialize_registers "
  writeReg cur_privilege (← (undefined_Privilege ()))
  dbg_trace "initialize_registers "
  writeReg cur_inst (← (undefined_bitvector ((2 ^i 3) *i 8)))
  dbg_trace "initialize_registers "
  writeReg mie (← (undefined_Minterrupts ()))
  dbg_trace "initialize_registers "
  writeReg mip (← (undefined_Minterrupts ()))
  dbg_trace "initialize_registers "
  writeReg medeleg (← (undefined_Medeleg ()))
  dbg_trace "initialize_registers "
  writeReg mideleg (← (undefined_Minterrupts ()))
  dbg_trace "initialize_registers "
  writeReg mtvec (← (undefined_Mtvec ()))
  dbg_trace "initialize_registers "
  writeReg mcause (← (undefined_Mcause ()))
  dbg_trace "initialize_registers "
  writeReg mepc (← (undefined_bitvector ((2 ^i 3) *i 8)))
  dbg_trace "initialize_registers "
  writeReg mtval (← (undefined_bitvector ((2 ^i 3) *i 8)))
  dbg_trace "initialize_registers "
  writeReg mscratch (← (undefined_bitvector ((2 ^i 3) *i 8)))
  dbg_trace "initialize_registers "
  writeReg scounteren (← (undefined_Counteren ()))
  dbg_trace "initialize_registers "
  writeReg mcounteren (← (undefined_Counteren ()))
  dbg_trace "initialize_registers "
  writeReg mcountinhibit (← (undefined_Counterin ()))
  dbg_trace "initialize_registers "
  writeReg mcycle (← (undefined_bitvector 64))
  dbg_trace "initialize_registers "
  writeReg mtime (← (undefined_bitvector 64))
  dbg_trace "initialize_registers "
  writeReg minstret (← (undefined_bitvector 64))
  dbg_trace "initialize_registers "
  writeReg minstret_increment (← (undefined_bool ()))
  dbg_trace "initialize_registers "
  writeReg stvec (← (undefined_Mtvec ()))
  dbg_trace "initialize_registers "
  writeReg sscratch (← (undefined_bitvector ((2 ^i 3) *i 8)))
  dbg_trace "initialize_registers "
  writeReg sepc (← (undefined_bitvector ((2 ^i 3) *i 8)))
  dbg_trace "initialize_registers "
  writeReg scause (← (undefined_Mcause ()))
  dbg_trace "initialize_registers "
  writeReg stval (← (undefined_bitvector ((2 ^i 3) *i 8)))
  dbg_trace "initialize_registers "
  writeReg tselect (← (undefined_bitvector ((2 ^i 3) *i 8)))
  dbg_trace "initialize_registers "
  writeReg vstart (← (undefined_bitvector 16))
  dbg_trace "initialize_registers "
  writeReg vl (← (undefined_bitvector ((2 ^i 3) *i 8)))
  dbg_trace "initialize_registers "
  writeReg vtype (← (undefined_Vtype ()))
  dbg_trace "initialize_registers "
  writeReg pmpcfg_n (← (undefined_vector 64 (← (undefined_Pmpcfg_ent ()))))
  dbg_trace "initialize_registers "
  writeReg pmpaddr_n (← (undefined_vector 64 (← (undefined_bitvector ((2 ^i 3) *i 8)))))
  dbg_trace "initialize_registers "
  writeReg vr0 (← (undefined_bitvector 65536))
  writeReg vr1 (← (undefined_bitvector 65536))
  writeReg vr2 (← (undefined_bitvector 65536))
  writeReg vr3 (← (undefined_bitvector 65536))
  writeReg vr4 (← (undefined_bitvector 65536))
  writeReg vr5 (← (undefined_bitvector 65536))
  writeReg vr6 (← (undefined_bitvector 65536))
  writeReg vr7 (← (undefined_bitvector 65536))
  writeReg vr8 (← (undefined_bitvector 65536))
  writeReg vr9 (← (undefined_bitvector 65536))
  writeReg vr10 (← (undefined_bitvector 65536))
  writeReg vr11 (← (undefined_bitvector 65536))
  writeReg vr12 (← (undefined_bitvector 65536))
  writeReg vr13 (← (undefined_bitvector 65536))
  writeReg vr14 (← (undefined_bitvector 65536))
  writeReg vr15 (← (undefined_bitvector 65536))
  writeReg vr16 (← (undefined_bitvector 65536))
  writeReg vr17 (← (undefined_bitvector 65536))
  writeReg vr18 (← (undefined_bitvector 65536))
  writeReg vr19 (← (undefined_bitvector 65536))
  writeReg vr20 (← (undefined_bitvector 65536))
  writeReg vr21 (← (undefined_bitvector 65536))
  writeReg vr22 (← (undefined_bitvector 65536))
  writeReg vr23 (← (undefined_bitvector 65536))
  writeReg vr24 (← (undefined_bitvector 65536))
  writeReg vr25 (← (undefined_bitvector 65536))
  writeReg vr26 (← (undefined_bitvector 65536))
  writeReg vr27 (← (undefined_bitvector 65536))
  writeReg vr28 (← (undefined_bitvector 65536))
  writeReg vr29 (← (undefined_bitvector 65536))
  writeReg vr30 (← (undefined_bitvector 65536))
  writeReg vr31 (← (undefined_bitvector 65536))
  dbg_trace "initialize_registers "
  writeReg vcsr (← (undefined_Vcsr ()))
  dbg_trace "initialize_registers "
  writeReg mhpmevent (← (undefined_vector 32 (← (undefined_HpmEvent ()))))
  dbg_trace "initialize_registers "
  writeReg mhpmcounter (← (undefined_vector 32 (← (undefined_bitvector 64))))
  dbg_trace "initialize_registers "
  writeReg mcyclecfg (← (undefined_CountSmcntrpmf ()))
  dbg_trace "initialize_registers "
  writeReg minstretcfg (← (undefined_CountSmcntrpmf ()))
  dbg_trace "initialize_registers "
  writeReg mtimecmp (← (undefined_bitvector 64))
  dbg_trace "initialize_registers "
  writeReg stimecmp (← (undefined_bitvector 64))
  dbg_trace "initialize_registers "
  writeReg htif_tohost (← (undefined_bitvector 64))
  dbg_trace "initialize_registers "
  writeReg htif_done (← (undefined_bool ()))
  dbg_trace "initialize_registers "
  writeReg htif_exit_code (← (undefined_bitvector 64))
  dbg_trace "initialize_registers "
  writeReg htif_cmd_write (← (undefined_bit ()))
  dbg_trace "initialize_registers "
  writeReg htif_payload_writes (← (undefined_bitvector 4))
  dbg_trace "initialize_registers "
  writeReg satp (← (undefined_bitvector ((2 ^i 3) *i 8)))

def sail_model_init (x_0 : Unit) : SailM Unit := do
  dbg_trace "sail_model_init 1"
  writeReg misa (_update_Misa_MXL (Mk_Misa (zeros_implicit (n := 64))) (architecture_forwards RV64))
  dbg_trace "sail_model_init 2"
  writeReg mstatus (let mxl := (architecture_forwards RV64)
  dbg_trace "sail_model_init 3"
  (_update_Mstatus_UXL
    (_update_Mstatus_SXL (Mk_Mstatus (zeros_implicit (n := 64)))
      (bif (Bool.and (bne xlen 32) (sys_enable_supervisor ()))
      then mxl
      else (zeros_implicit (n := 2))))
    (bif (Bool.and (bne xlen 32) (sys_enable_user ()))
    then mxl
    else (zeros_implicit (n := 2)))))
  dbg_trace "sail_model_init 4"
  writeReg menvcfg (← (legalize_menvcfg (Mk_MEnvcfg (zeros_implicit (n := 64)))
      (zeros_implicit (n := 64))))
  dbg_trace "sail_model_init 5"
  writeReg senvcfg (← (legalize_senvcfg (Mk_SEnvcfg (zeros_implicit (n := 64)))
      (zeros_implicit (n := ((2 ^i 3) *i 8)))))
  dbg_trace "sail_model_init 6"
  writeReg minstret_write none
  dbg_trace "sail_model_init 7"
  writeReg minstreth_write none
  dbg_trace "sail_model_init 8"
  writeReg mvendorid (zeros_implicit (n := 32))
  dbg_trace "sail_model_init 9"
  writeReg mimpid (zeros_implicit (n := ((2 ^i 3) *i 8)))
  dbg_trace "sail_model_init 10"
  writeReg marchid (zeros_implicit (n := ((2 ^i 3) *i 8)))
  dbg_trace "sail_model_init 11"
  writeReg mhartid (zeros_implicit (n := ((2 ^i 3) *i 8)))
  dbg_trace "sail_model_init 12"
  writeReg mconfigptr (zeros_implicit (n := ((2 ^i 3) *i 8)))
  dbg_trace "sail_model_init 13"
  writeReg tlb (vectorInit none)
  dbg_trace "sail_model_init 14"
  (initialize_registers ())

end LeanRV64DLEAN.Functions

open LeanRV64DLEAN.Functions

/- def main (_ : List String) : IO UInt32 := do -/
/-   main_of_sail_main ⟨default, (), default, default, default, default⟩ (sail_model_init >=> sail_main) -/
