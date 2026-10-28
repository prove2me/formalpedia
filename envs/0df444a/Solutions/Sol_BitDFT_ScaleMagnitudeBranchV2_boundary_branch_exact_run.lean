-- Prove2me | solution 1 for BitDFT.ScaleMagnitudeBranchV2.boundary_branch_exact_run
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T22:17:17.511898+00:00
-- url     : https://prove2.me/submissions/222bf03a-433b-4f31-bed4-098d61d18343

import Definitions.Def_BitDFT_ScaleMagnitudeBranchV2
import Theorems.Thm_BitDFT_BoundaryShiftEmitter_boundary_shift_emit_run
import Theorems.Thm_BitDFT_MachineSequence_branchController_run_left_no_early
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 0

open BitDFT BitDFT.ScaleMagnitudeBranchV2 BitDFT.BoundaryShiftEmitter BitDFT.MachineSequence IntMul

theorem solution {N : MultitapeTM}
    (selector coordinate dimension output : Fin N.k) (isHigh : N.Sym → Bool)
    (hc : coordinate ≠ N.inTape) (hd : dimension ≠ N.inTape) (ho : output ≠ N.inTape)
    (hcd : coordinate ≠ dimension) (hco : coordinate ≠ output) (hdo : dimension ≠ output)
    (hsc : selector ≠ coordinate) (hsd : selector ≠ dimension) (hso : selector ≠ output)
    (base : (BoundaryShiftEmitter.control N coordinate dimension output hc hd ho hcd hco hdo).machine.Cfg)
    (sign high : Bool) (dimensionBits low : List Bool)
    (hflag : isHigh (base.cells selector (base.head selector)) = true) :
    let P := BoundaryShiftEmitter.control N coordinate dimension output hc hd ho hcd hco hdo
    let initial := BoundaryShiftEmitter.frame coordinate dimension output hc hd ho hcd hco hdo
      base .sign ([sign, high] ++ low) dimensionBits [] 1 1 1
    (machine N selector coordinate dimension output isHigh hc hd ho hcd hco hdo hsc hsd hso).step^[dimensionBits.length+low.length+6]
      (branchChooseCfg initial.cells initial.head) =
      branchDoneCfg (source := selector) (test := isHigh)
        (P := BoundaryShiftEmitter.control N coordinate dimension output hc hd ho hcd hco hdo)
        (Q := MachineSequence.native N)
        (P.machine.step^[dimensionBits.length+low.length+4] initial).cells
        (P.machine.step^[dimensionBits.length+low.length+4] initial).head := by
  let P := BoundaryShiftEmitter.control N coordinate dimension output hc hd ho hcd hco hdo
  let Q := MachineSequence.native N
  let initial := BoundaryShiftEmitter.frame coordinate dimension output hc hd ho hcd hco hdo
    base .sign ([sign, high] ++ low) dimensionBits [] 1 1 1
  have hflag' : isHigh (initial.cells selector (initial.head selector)) = true := by
    simpa [initial, BoundaryShiftEmitter.frame, hsc, hsd, hso] using hflag
  have hrun := BoundaryShiftEmitter.boundary_shift_emit_run N coordinate dimension output
    hc hd ho hcd hco hdo base sign high dimensionBits low
  have hexit : (P.machine.step^[dimensionBits.length+low.length+4] initial).state = P.exit := by
    rw [hrun]
    rfl
  have hcombined := branchController_run_left_no_early selector isHigh P Q
    (dimensionBits.length+low.length+4) initial rfl hflag' hexit
  change (branchController selector isHigh P Q).machine.step^[dimensionBits.length+low.length+6]
      (branchChooseCfg initial.cells initial.head) =
      branchDoneCfg (source := selector) (test := isHigh) (P := P) (Q := Q)
        (P.machine.step^[dimensionBits.length+low.length+4] initial).cells
        (P.machine.step^[dimensionBits.length+low.length+4] initial).head
  exact hcombined
