-- Prove2me | solution 1 for BitDFT.BankedOperandStageProof.coordinate_pair_output_buffer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T16:45:15.255571+00:00
-- url     : https://prove2.me/submissions/17a6a559-daf2-4f14-8bbb-2ed036f274c1

import Definitions.Def_BitDFT_OperandStage
import Definitions.Def_BitDFT_BankedOperandStageProofSupport
import Theorems.Thm_BitDFT_BankedOperandStageProof_coordinate_pair_to_halt
import Mathlib.Data.List.GetD
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
namespace BitDFT.BankedOperandStageProof
open IntMul BitDFT.OperandStage BitDFT.MachineSequence BitDFT.BankedOperandStageProofSupport

theorem coordinate_pair_output_buffer_proof {N : MultitapeTM}
    (coord dim out : Fin N.k)
    (hc : coord ≠ N.inTape) (hd : dim ≠ N.inTape) (ho : out ≠ N.inTape)
    (hcd : coord ≠ dim) (hco : coord ≠ out) (hdo : dim ≠ out)
    (base : (control N coord dim out hc hd ho hcd hco hdo).machine.Cfg)
    (dimension low : List Bool) (sign high : Bool)
    (hdimCells : base.cells dim = N.tapeOf (dimension.map N.bitSym))
    (hdimHead : base.head dim = dimension.length + 1)
    (hcoordCells : base.cells coord = N.tapeOf (([sign, high] ++ low).map N.bitSym))
    (hcoordHead : base.head coord = low.length + 3)
    (hq : dimension.length ≤ low.length)
    (hpad : ∀ p, 1 ≤ p →
      (N.tapeOf (N.blank :: List.replicate low.length N.zero)) p ≠ N.startSym)
    (hdimBlank : (N.tapeOf (dimension.map N.bitSym))
      (dimension.length + 1) = N.blank) :
    ((machine N coord dim out hc hd ho hcd hco hdo).step ^[
      2 * dimension.length + 3 * low.length + 14]
      (initialStageFrame coord dim out hc hd ho hcd hco hdo base
        ([sign, high] ++ low))).cells out =
      N.tapeOf (N.blank ::
        (List.replicate (low.length - dimension.length) N.zero ++
          dimension.map N.bitSym ++ [N.sep] ++ low.map N.bitSym)) := by
  have hrun := coordinate_pair_to_halt coord dim out hc hd ho hcd hco hdo
    base dimension low sign high hdimCells hdimHead hcoordCells hcoordHead hq hpad hdimBlank
  rw [hrun]
  simp [coordinateCopyFrame, hco, Ne.symm hco]

end BitDFT.BankedOperandStageProof
end

abbrev solution := @BitDFT.BankedOperandStageProof.coordinate_pair_output_buffer_proof
