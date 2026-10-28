-- Prove2me | solution 1 for BitDFT.ReaderOutputStageRun.reader_outputs_stage_halt_with_work_v2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T18:18:02.783348+00:00
-- url     : https://prove2.me/submissions/2855e7d3-1fcb-4089-a8f1-b5fb5c3c1760

import Definitions.Def_BitDFT_BankedOperandStageProofSupport
import Definitions.Def_BitDFT_OperandStage
import Definitions.Def_BitDFT_ReaderHostFrame_WorkSupport_v2
import Definitions.Def_BitDFT_ReaderOutputStageSupport
import Theorems.Thm_BitDFT_ReaderHostFrame_reader_outputs_to_operand_frame_with_work_v3
import Theorems.Thm_BitDFT_OperandStage_run_preserves_other_tape
import Theorems.Thm_BitDFT_BankedOperandStageProof_coordinate_pair_to_halt
import Theorems.Thm_BitDFT_BankedOperandStageProof_coordinate_pair_output_buffer
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open IntMul BitDFT.OperandStage BitDFT.MachineSequence
namespace BitDFT.ReaderOutputStageRun
theorem solution
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
    ∃ base : (BitDFT.OperandStage.control N coord dim out hc hd ho hcd hco hdo).machine.Cfg,
      base.cells dim = N.tapeOf (dimension.map N.bitSym) ∧
      base.head dim = dimension.length + 1 ∧
      base.cells coord = N.tapeOf (([sign, high] ++ low).map N.bitSym) ∧
      base.head coord = low.length + 3 ∧
      (∀ i : Fin (M.k + 2), 2 ≤ i.val →
        base.cells (BitDFT.ReaderHostFrame.multiplierTapeRoute A M H i) = N.tapeOf [] ∧
        base.head (BitDFT.ReaderHostFrame.multiplierTapeRoute A M H i) = 1) ∧
      ∃ final : (BitDFT.OperandStage.control N coord dim out hc hd ho hcd hco hdo).machine.Cfg,
        (BitDFT.OperandStage.control N coord dim out hc hd ho hcd hco hdo).machine.step ^[
          2 * dimension.length + 3 * low.length + 14]
          (@BitDFT.ReaderOutputStageRun.entryFrame N coord dim out hc hd ho hcd hco hdo base
            ([sign, high] ++ low)) = final ∧
        final.state = BitDFT.OperandStage.State.halt ∧
        final.cells out = N.tapeOf (N.blank ::
          (List.replicate (low.length - dimension.length) N.zero ++
            dimension.map N.bitSym ++ [N.sep] ++ low.map N.bitSym)) ∧
        (∀ i : Fin (M.k + 2), 2 ≤ i.val →
          final.cells (BitDFT.ReaderHostFrame.multiplierTapeRoute A M H i) = N.tapeOf [] ∧
          final.head (BitDFT.ReaderHostFrame.multiplierTapeRoute A M H i) = 1) := by
  dsimp
  let N := BitDFT.ReaderHostFrame.host A M H
  let coord := BitDFT.BankedOperandStage.coordinateTape A M H j
  let dim := BitDFT.BankedOperandStage.dimensionTape A M H
  let out := BitDFT.BankedOperandStage.multiplierOutputTape A M H
  let P := BitDFT.OperandStage.control N coord dim out hc hd ho hcd hco hdo
  obtain ⟨base, hdCells, hdHead, hcCells, hcHead, hworkBase⟩ :=
    BitDFT.ReaderHostFrame.reader_outputs_to_operand_frame_with_work_v3
      A M H hH4 cF cH j hj dimension low sign high hcoord hdim hdimHead
  have hrun := BitDFT.BankedOperandStageProof.coordinate_pair_to_halt
    coord dim out hc hd ho hcd hco hdo base dimension low sign high
    hdCells hdHead hcCells hcHead hq hpad hdimBlank
  have hbuffer := BitDFT.BankedOperandStageProof.coordinate_pair_output_buffer
    coord dim out hc hd ho hcd hco hdo base dimension low sign high
    hdCells hdHead hcCells hcHead hq hpad hdimBlank
  let final : P.machine.Cfg :=
      ⟨BitDFT.OperandStage.State.halt,
        (BitDFT.BankedOperandStageProofSupport.coordinateCopyFrame coord dim out hc hd ho hcd hco hdo
          base ([sign, high] ++ low)
          (List.replicate (low.length - dimension.length) N.zero ++ dimension.map N.bitSym ++
            [N.sep] ++ low.map N.bitSym)
          (low.length + 3)
          ((List.replicate (low.length - dimension.length) N.zero ++
            dimension.map N.bitSym ++ [N.sep]).length + low.length + 2)).cells,
        (BitDFT.BankedOperandStageProofSupport.coordinateCopyFrame coord dim out hc hd ho hcd hco hdo
          base ([sign, high] ++ low)
          (List.replicate (low.length - dimension.length) N.zero ++ dimension.map N.bitSym ++
            [N.sep] ++ low.map N.bitSym)
          (low.length + 3)
          ((List.replicate (low.length - dimension.length) N.zero ++
            dimension.map N.bitSym ++ [N.sep]).length + low.length + 2)).head⟩
  have hEntry : @BitDFT.ReaderOutputStageRun.entryFrame N coord dim out hc hd ho hcd hco hdo base
      ([sign, high] ++ low) =
      @BitDFT.BankedOperandStageProofSupport.initialStageFrame N coord dim out hc hd ho hcd hco hdo
        base ([sign, high] ++ low) := by rfl
  have hrun' : P.machine.step^[2 * dimension.length + 3 * low.length + 14]
      (@BitDFT.ReaderOutputStageRun.entryFrame N coord dim out hc hd ho hcd hco hdo base
        ([sign, high] ++ low)) = final := by
    rw [hEntry]
    simpa [final] using hrun
  have hstate : final.state = BitDFT.OperandStage.State.halt := by rfl
  have hout : final.cells out = N.tapeOf (N.blank ::
      (List.replicate (low.length - dimension.length) N.zero ++
        dimension.map N.bitSym ++ [N.sep] ++ low.map N.bitSym)) := by
    rw [← hrun']
    change (P.machine.step^[2 * dimension.length + 3 * low.length + 14]
      (@BitDFT.ReaderOutputStageRun.entryFrame N coord dim out hc hd ho hcd hco hdo base
        ([sign, high] ++ low))).cells out = _
    rw [hEntry]
    simpa [BitDFT.BankedOperandStageProofSupport.coordinateCopyFrame, hco, hdo] using hbuffer
  have hworkFinal : ∀ i : Fin (M.k + 2), 2 ≤ i.val →
      final.cells (BitDFT.ReaderHostFrame.multiplierTapeRoute A M H i) = N.tapeOf [] ∧
      final.head (BitDFT.ReaderHostFrame.multiplierTapeRoute A M H i) = 1 := by
    intro i hi
    let p := BitDFT.ReaderHostFrame.multiplierTapeRoute A M H i
    have hpVal : p.val = A.k + i.val - 1 := by
      have h := BitDFT.DedicatedTapeBanks.multiplier_work_address A
        (BitDFT.ReaderHostFrame.tracked M) H i (by omega)
      have hv := congrArg Fin.val h
      simpa [p, BitDFT.ReaderHostFrame.multiplierTapeRoute,
        BitDFT.ReaderHostFrame.tracked, BitDFT.BankedTripleAlphabetHost.route,
        BitDFT.TapeExtension.oldTape, Fin.cast] using hv
    have hpCoord : p ≠ coord := by
      intro he
      have hv := congrArg Fin.val he
      rw [hpVal] at hv
      simp [p, coord, BitDFT.ReaderHostFrame.multiplierTapeRoute,
        BitDFT.ReaderHostFrame.tracked, BitDFT.BankedOperandStage.coordinateTape] at hv
      omega
    have hpDim : p ≠ dim := by
      intro he
      have hv := congrArg Fin.val he
      rw [hpVal] at hv
      simp [p, dim, BitDFT.ReaderHostFrame.multiplierTapeRoute,
        BitDFT.ReaderHostFrame.tracked, BitDFT.BankedOperandStage.dimensionTape] at hv
      omega
    have hpOut : p ≠ out := by
      intro he
      have hv := congrArg Fin.val he
      rw [hpVal] at hv
      simp [p, out, BitDFT.ReaderHostFrame.multiplierTapeRoute,
        BitDFT.ReaderHostFrame.tracked, BitDFT.BankedOperandStage.multiplierOutputTape] at hv
      omega
    have hpres := BitDFT.OperandStage.run_preserves_other_tape (N := N)
      coord dim out hc hd ho hcd hco hdo
      (@BitDFT.ReaderOutputStageRun.entryFrame N coord dim out hc hd ho hcd hco hdo base
        ([sign, high] ++ low)) p hpCoord hpDim hpOut
      (2 * dimension.length + 3 * low.length + 14)
    have hentryCells :
        (@BitDFT.ReaderOutputStageRun.entryFrame N coord dim out hc hd ho hcd hco hdo base
          ([sign, high] ++ low)).cells p = base.cells p := by
      by_cases hpc : p = coord
      · exact (hpCoord hpc).elim
      · by_cases hpo : p = out
        · exact (hpOut hpo).elim
        · change (if p = coord then N.tapeOf (([sign, high] ++ low).map N.bitSym)
            else if p = out then N.tapeOf [] else base.cells p) = base.cells p
          simp [hpc, hpo]
    have hentryHead :
        (@BitDFT.ReaderOutputStageRun.entryFrame N coord dim out hc hd ho hcd hco hdo base
          ([sign, high] ++ low)).head p = base.head p := by
      by_cases hpc : p = coord
      · exact (hpCoord hpc).elim
      · by_cases hpo : p = out
        · exact (hpOut hpo).elim
        · change (if p = coord ∨ p = out then 1 else base.head p) = base.head p
          simp [hpc, hpo]
    have hbase := hworkBase i hi
    constructor
    · calc
        final.cells p = (P.machine.step^[2 * dimension.length + 3 * low.length + 14]
          (@BitDFT.ReaderOutputStageRun.entryFrame N coord dim out hc hd ho hcd hco hdo base
            ([sign, high] ++ low))).cells p := by rw [hrun']
        _ = base.cells p := hpres.1.trans hentryCells
        _ = N.tapeOf [] := hbase.1
    · calc
        final.head p = (P.machine.step^[2 * dimension.length + 3 * low.length + 14]
          (@BitDFT.ReaderOutputStageRun.entryFrame N coord dim out hc hd ho hcd hco hdo base
            ([sign, high] ++ low))).head p := by rw [hrun']
        _ = base.head p := hpres.2.trans hentryHead
        _ = 1 := hbase.2
  exact ⟨base, hdCells, hdHead, hcCells, hcHead, hworkBase, final, hrun', hstate, hout, hworkFinal⟩

end BitDFT.ReaderOutputStageRun
end

abbrev solution := @BitDFT.ReaderOutputStageRun.solution
