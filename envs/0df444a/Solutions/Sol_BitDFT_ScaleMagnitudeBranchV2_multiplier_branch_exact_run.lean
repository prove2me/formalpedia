-- Prove2me | solution 1 for BitDFT.ScaleMagnitudeBranchV2.multiplier_branch_exact_run
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T22:17:00.834849+00:00
-- url     : https://prove2.me/submissions/37d3b1ac-0843-44e6-9e13-bf31afe4cbb0

import Definitions.Def_BitDFT_ScaleMagnitudeBranchV2
import Theorems.Thm_BitDFT_MachineSequence_branchController_run_right_no_early
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 0

open BitDFT BitDFT.ScaleMagnitudeBranchV2 BitDFT.BoundaryShiftEmitter BitDFT.MachineSequence IntMul

theorem solution {N : MultitapeTM}
    (selector coordinate dimension output : Fin N.k) (isHigh : N.Sym → Bool)
    (hc : coordinate ≠ N.inTape) (hd : dimension ≠ N.inTape) (ho : output ≠ N.inTape)
    (hcd : coordinate ≠ dimension) (hco : coordinate ≠ output) (hdo : dimension ≠ output)
    (hsc : selector ≠ coordinate) (hsd : selector ≠ dimension) (hso : selector ≠ output)
    (t : ℕ) (c : N.Cfg) (hentry : c.state = N.qStart)
    (hflag : isHigh (c.cells selector (c.head selector)) = false)
    (hexit : (N.step^[t] c).state = N.qHalt) :
    (machine N selector coordinate dimension output isHigh hc hd ho hcd hco hdo hsc hsd hso).step^[t+2]
      (branchChooseCfg c.cells c.head) =
      branchDoneCfg (source := selector) (test := isHigh)
        (P := BoundaryShiftEmitter.control N coordinate dimension output hc hd ho hcd hco hdo)
        (Q := MachineSequence.native N) (N.step^[t] c).cells (N.step^[t] c).head := by
  let P := BoundaryShiftEmitter.control N coordinate dimension output hc hd ho hcd hco hdo
  let Q := MachineSequence.native N
  have hcombined := branchController_run_right_no_early selector isHigh P Q t c
    hentry hflag hexit
  change (branchController selector isHigh P Q).machine.step^[t+2]
      (branchChooseCfg c.cells c.head) =
      branchDoneCfg (source := selector) (test := isHigh) (P := P) (Q := Q)
        (N.step^[t] c).cells (N.step^[t] c).head
  simpa [P, Q, MachineSequence.native, Controller.machine] using hcombined
