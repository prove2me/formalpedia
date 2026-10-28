-- Prove2me | solution 1 for BitDFT.ReaderOutputStageRun.reader_outputs_stage_buffer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T16:48:20.178216+00:00
-- url     : https://prove2.me/submissions/ef4aa3b4-9c93-4f66-b85a-8113a9005ad4

import Definitions.Def_BitDFT_ReaderOutputStageRun
import Theorems.Thm_BitDFT_BankedOperandStageProof_coordinate_pair_output_buffer
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
namespace BitDFT.ReaderOutputStageRun
open IntMul BitDFT.OperandStage

theorem reader_outputs_stage_buffer_proof
    (A M H : MultitapeTM) (hH4 : 3 < H.k)
    (cF : A.Cfg) (cH : H.Cfg) (j : Fin A.k) (hj : 1 ≤ j.val)
    (dimension low : List Bool) (sign high : Bool)
    (hcoord : cF.cells j = A.tapeOf (([sign, high] ++ low).map A.bitSym))
    (hdim : cH.cells ⟨3, hH4⟩ = H.tapeOf (dimension.map H.bitSym))
    (hdimHead : cH.head ⟨3, hH4⟩ = dimension.length + 1)
    (hq : dimension.length ≤ low.length)
    (hc : BitDFT.BankedOperandStage.coordinateTape A M H j ≠
      (BitDFT.ReaderHostFrame.host A M H).inTape)
    (hd : BitDFT.BankedOperandStage.dimensionTape A M H ≠
      (BitDFT.ReaderHostFrame.host A M H).inTape)
    (ho : BitDFT.BankedOperandStage.multiplierOutputTape A M H ≠
      (BitDFT.ReaderHostFrame.host A M H).inTape)
    (hcd : BitDFT.BankedOperandStage.coordinateTape A M H j ≠
      BitDFT.BankedOperandStage.dimensionTape A M H)
    (hco : BitDFT.BankedOperandStage.coordinateTape A M H j ≠
      BitDFT.BankedOperandStage.multiplierOutputTape A M H)
    (hdo : BitDFT.BankedOperandStage.dimensionTape A M H ≠
      BitDFT.BankedOperandStage.multiplierOutputTape A M H)
    (hpad : ∀ p, 1 ≤ p →
      ((BitDFT.ReaderHostFrame.host A M H).tapeOf
        ((BitDFT.ReaderHostFrame.host A M H).blank ::
          List.replicate low.length (BitDFT.ReaderHostFrame.host A M H).zero)) p ≠
          (BitDFT.ReaderHostFrame.host A M H).startSym)
    (hdimBlank : ((BitDFT.ReaderHostFrame.host A M H).tapeOf
      (dimension.map (BitDFT.ReaderHostFrame.host A M H).bitSym))
        (dimension.length + 1) = (BitDFT.ReaderHostFrame.host A M H).blank) :
    let N := BitDFT.ReaderHostFrame.host A M H
    let coord := BitDFT.BankedOperandStage.coordinateTape A M H j
    let dim := BitDFT.BankedOperandStage.dimensionTape A M H
    let out := BitDFT.BankedOperandStage.multiplierOutputTape A M H
    ∃ base : (BitDFT.BankedOperandStage.controller A M H j hj).machine.Cfg,
      base.cells dim = N.tapeOf (dimension.map N.bitSym) ∧
      base.head dim = dimension.length + 1 ∧
      base.cells coord = N.tapeOf (([sign, high] ++ low).map N.bitSym) ∧
      base.head coord = low.length + 3 ∧
      ((BitDFT.OperandStage.control N coord dim out hc hd ho hcd hco hdo).machine.step ^[
        2 * dimension.length + 3 * low.length + 14]
        (@BitDFT.ReaderOutputStageRun.entryFrame N coord dim out hc hd ho hcd hco hdo base
          ([sign, high] ++ low))).cells out =
        N.tapeOf (N.blank ::
          (List.replicate (low.length - dimension.length) N.zero ++
            dimension.map N.bitSym ++ [N.sep] ++ low.map N.bitSym)) := by
  dsimp
  obtain ⟨base, hdCells, hdHead, hcCells, hcHead⟩ :=
    BitDFT.ReaderHostFrame.reader_outputs_to_operand_frame A M H hH4 cF cH j hj
      dimension low sign high hcoord hdim hdimHead
  refine ⟨base, hdCells, hdHead, hcCells, hcHead, ?_⟩
  exact BitDFT.BankedOperandStageProof.coordinate_pair_output_buffer
    (N := BitDFT.ReaderHostFrame.host A M H)
    (BitDFT.BankedOperandStage.coordinateTape A M H j)
    (BitDFT.BankedOperandStage.dimensionTape A M H)
    (BitDFT.BankedOperandStage.multiplierOutputTape A M H)
    hc hd ho hcd hco hdo base dimension low sign high
    hdCells hdHead hcCells hcHead hq hpad hdimBlank

end BitDFT.ReaderOutputStageRun
end

abbrev solution := @BitDFT.ReaderOutputStageRun.reader_outputs_stage_buffer_proof
