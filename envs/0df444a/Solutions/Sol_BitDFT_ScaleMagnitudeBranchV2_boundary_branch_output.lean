-- Prove2me | solution 1 for BitDFT.ScaleMagnitudeBranchV2.boundary_branch_output
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T22:29:53.455175+00:00
-- url     : https://prove2.me/submissions/9facda0b-d7af-4fea-924f-221586db6e16

import Definitions.Def_BitDFT_ScaleMagnitudeBranchV2
import Definitions.Def_BitDFT_BoundaryShiftEmitter
import Definitions.Def_BitDFT_MachineSequence
import Theorems.Thm_BitDFT_ScaleMagnitudeBranchV2_boundary_branch_exact_run
import Theorems.Thm_BitDFT_BoundaryShiftEmitter_boundary_shift_emit_run

set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section

open IntMul BitDFT.MachineSequence

/-- The selected boundary branch writes the full signed scaled coordinate to
the designated output tape, not merely reaching the emitter's halt state. -/
theorem solution
    {N : MultitapeTM}
    (selector coordinate dimension output : Fin N.k) (isHigh : N.Sym → Bool)
    (hc : coordinate ≠ N.inTape) (hd : dimension ≠ N.inTape)
    (ho : output ≠ N.inTape) (hcd : coordinate ≠ dimension)
    (hco : coordinate ≠ output) (hdo : dimension ≠ output)
    (hsc : selector ≠ coordinate) (hsd : selector ≠ dimension)
    (hso : selector ≠ output)
    (base : (BitDFT.BoundaryShiftEmitter.control N coordinate dimension output
      hc hd ho hcd hco hdo).machine.Cfg)
    (sign high : Bool) (dimensionBits low : List Bool)
    (hflag : isHigh (base.cells selector (base.head selector)) = true) :
    let P := BitDFT.BoundaryShiftEmitter.control N coordinate dimension output
      hc hd ho hcd hco hdo
    let initial := BitDFT.BoundaryShiftEmitter.frame coordinate dimension output
      hc hd ho hcd hco hdo base .sign ([sign, high] ++ low) dimensionBits [] 1 1 1
    let result := (branchController selector isHigh P (BitDFT.MachineSequence.native N)).machine.step^[dimensionBits.length + low.length + 6]
      (branchChooseCfg initial.cells initial.head)
    result.cells output = N.tapeOf
      (([sign] ++ dimensionBits ++ List.replicate low.length false).map N.bitSym) := by
  let P := BitDFT.BoundaryShiftEmitter.control N coordinate dimension output
    hc hd ho hcd hco hdo
  let Q := BitDFT.MachineSequence.native N
  let initial := BitDFT.BoundaryShiftEmitter.frame coordinate dimension output
    hc hd ho hcd hco hdo base .sign ([sign, high] ++ low) dimensionBits [] 1 1 1
  let result := (branchController selector isHigh P Q).machine.step^[dimensionBits.length + low.length + 6]
    (branchChooseCfg initial.cells initial.head)
  have hbranch := BitDFT.ScaleMagnitudeBranchV2.boundary_branch_exact_run
    selector coordinate dimension output isHigh hc hd ho hcd hco hdo hsc hsd hso
    base sign high dimensionBits low hflag
  have hrun := BitDFT.BoundaryShiftEmitter.boundary_shift_emit_run N coordinate
    dimension output hc hd ho hcd hco hdo base sign high dimensionBits low
  have hcells : result.cells output =
      (P.machine.step^[dimensionBits.length + low.length + 4] initial).cells output := by
    change ((branchController selector isHigh P Q).machine.step^[dimensionBits.length + low.length + 6]
      (branchChooseCfg initial.cells initial.head)).cells output = _
    change (branchController selector isHigh P Q).machine.step^[dimensionBits.length + low.length + 6]
      (branchChooseCfg initial.cells initial.head) =
      @branchDoneCfg N selector isHigh P Q
        (P.machine.step^[dimensionBits.length + low.length + 4] initial).cells
        (P.machine.step^[dimensionBits.length + low.length + 4] initial).head at hbranch
    rw [hbranch]
    rfl
  have hfinal : (P.machine.step^[dimensionBits.length + low.length + 4] initial).cells output =
      N.tapeOf (([sign] ++ dimensionBits ++ List.replicate low.length false).map N.bitSym) := by
    rw [hrun]
    simp [P, BitDFT.BoundaryShiftEmitter.frame, Ne.symm hco, Ne.symm hdo]
  change result.cells output = _
  rw [hcells]
  exact hfinal

end
