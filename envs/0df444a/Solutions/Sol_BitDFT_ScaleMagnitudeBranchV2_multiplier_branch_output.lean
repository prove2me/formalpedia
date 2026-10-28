-- Prove2me | solution 1 for BitDFT.ScaleMagnitudeBranchV2.multiplier_branch_output
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T22:42:50.187129+00:00
-- url     : https://prove2.me/submissions/d5e0182d-62ce-4f03-b7aa-bdd01b43895d

import Definitions.Def_BitDFT_ScaleMagnitudeBranchV2
import Definitions.Def_BitDFT_BoundaryShiftEmitter
import Definitions.Def_BitDFT_MachineSequence
import Theorems.Thm_BitDFT_ScaleMagnitudeBranchV2_multiplier_branch_exact_run

set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section

open IntMul BitDFT.MachineSequence

open BitDFT BitDFT.BoundaryShiftEmitter BitDFT.ScaleMagnitudeBranchV2

/-- The low-magnitude branch preserves the complete output tape of its
multiplier run. This makes the branch theorem usable as an output-frame
component when the multiplier controller is composed with the scaler. -/
theorem solution {N : MultitapeTM}
    (selector coordinate dimension output : Fin N.k) (isHigh : N.Sym → Bool)
    (hc : coordinate ≠ N.inTape) (hd : dimension ≠ N.inTape) (ho : output ≠ N.inTape)
    (hcd : coordinate ≠ dimension) (hco : coordinate ≠ output) (hdo : dimension ≠ output)
    (hsc : selector ≠ coordinate) (hsd : selector ≠ dimension) (hso : selector ≠ output)
    (c : N.Cfg)
    (hentry : c.state = N.qStart)
    (hflag : isHigh (c.cells selector (c.head selector)) = false)
    (t : ℕ) (hhalt : (N.step^[t] c).state = N.qHalt) :
    ((machine N selector coordinate dimension output isHigh hc hd ho hcd hco hdo hsc hsd hso).step^[t+2]
      (branchChooseCfg c.cells c.head)).cells output = (N.step^[t] c).cells output := by
  have hrun := multiplier_branch_exact_run selector coordinate dimension output isHigh
    hc hd ho hcd hco hdo hsc hsd hso t c hentry hflag hhalt
  let P := BoundaryShiftEmitter.control N coordinate dimension output hc hd ho hcd hco hdo
  let Q := MachineSequence.native N
  have hrun' : (branchController selector isHigh P Q).machine.step^[t+2]
      (branchChooseCfg c.cells c.head) =
      branchDoneCfg (N.step^[t] c).cells (N.step^[t] c).head := by
    simpa [P, Q, BitDFT.ScaleMagnitudeBranchV2.machine,
      BitDFT.ScaleMagnitudeBranchV2.controller] using hrun
  change ((branchController selector isHigh P Q).machine.step^[t+2]
      (branchChooseCfg c.cells c.head)).cells output = _
  rw [hrun']
  rfl

end
