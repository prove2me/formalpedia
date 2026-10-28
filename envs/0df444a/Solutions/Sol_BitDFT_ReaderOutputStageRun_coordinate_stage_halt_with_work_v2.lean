-- Prove2me | solution 1 for BitDFT.ReaderOutputStageRun.coordinate_stage_halt_with_work_v2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T06:13:29.828337+00:00
-- url     : https://prove2.me/submissions/90dcbc08-cffd-40aa-bc95-a9f62fed1a90

import Definitions.Def_BitDFT_BankedOperandStageProofSupport
import Definitions.Def_BitDFT_BankedTripleAlphabetHost
import Definitions.Def_BitDFT_BankedOperandStage
import Definitions.Def_BitDFT_TripleAlphabet
import Definitions.Def_IntMul_TrackedBankedCall
import Definitions.Def_BitDFT_OperandStage
import Theorems.Thm_BitDFT_OperandStage_run_preserves_other_tape
import Theorems.Thm_BitDFT_BankedOperandStageProof_coordinate_pair_to_halt
import Theorems.Thm_BitDFT_BankedOperandStageProof_coordinate_pair_output_buffer
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open IntMul BitDFT.OperandStage BitDFT.MachineSequence
namespace BitDFT.CPLocal
open IntMul BitDFT.DedicatedTapeBanks BitDFT.BankedTripleAlphabetHost
abbrev tracked (M : MultitapeTM) := IntMul.TrackedBankedCall.machine M
abbrev host (A M H : MultitapeTM) := BankedTripleAlphabetHost.multiplierMachine A (tracked M) H

def multiplierTapeRoute (A M H : MultitapeTM) (i : Fin (tracked M).k) :
    Fin (DedicatedTapeBanks.width A (tracked M) H) := by
  let X := tracked M
  have hX : X.k ≤ DedicatedTapeBanks.width A X H := by
    rw [DedicatedTapeBanks.width_eq_sum]
    have hA := A.two_le_k
    have hX := X.two_le_k
    have hH := H.two_le_k
    omega
  let r := DedicatedTapeBanks.width A X H - X.k
  let h : X.k + r = DedicatedTapeBanks.width A X H := Nat.add_sub_of_le hX
  exact BankedTripleAlphabetHost.route A X H
    (DedicatedTapeBanks.multiplierOffset A X H)
    (by
      have hA := A.two_le_k
      have hX := X.two_le_k
      have hH := H.two_le_k
      dsimp [DedicatedTapeBanks.multiplierOffset, DedicatedTapeBanks.tail]
      omega)
    (Fin.cast h (TapeExtension.oldTape X r i))


end BitDFT.CPLocal
namespace BitDFT.CPLocal
def entryFrame {N : MultitapeTM} (coord dim out : Fin N.k)
    (hc : coord ≠ N.inTape) (hd : dim ≠ N.inTape) (ho : out ≠ N.inTape)
    (hcd : coord ≠ dim) (hco : coord ≠ out) (hdo : dim ≠ out)
    (base : (BitDFT.OperandStage.control N coord dim out hc hd ho hcd hco hdo).machine.Cfg)
    (source : List Bool) :
    (BitDFT.OperandStage.control N coord dim out hc hd ho hcd hco hdo).machine.Cfg where
  state := .skipSign
  cells := fun i => if i = coord then N.tapeOf (source.map N.bitSym)
    else if i = out then N.tapeOf [] else base.cells i
  head := fun i => if i = coord ∨ i = out then 1 else base.head i

end BitDFT.CPLocal

theorem solution
    (A M H : MultitapeTM) (j : Fin A.k)
    (dimension low : List Bool) (sign high : Bool)
    (hq : dimension.length ≤ low.length)
    (hc : BitDFT.BankedOperandStage.coordinateTape A M H j ≠
      (BitDFT.CPLocal.host A M H).inTape)
    (hd : BitDFT.BankedOperandStage.dimensionTape A M H ≠
      (BitDFT.CPLocal.host A M H).inTape)
    (ho : BitDFT.BankedOperandStage.multiplierOutputTape A M H ≠
      (BitDFT.CPLocal.host A M H).inTape)
    (hcd : BitDFT.BankedOperandStage.coordinateTape A M H j ≠
      BitDFT.BankedOperandStage.dimensionTape A M H)
    (hco : BitDFT.BankedOperandStage.coordinateTape A M H j ≠
      BitDFT.BankedOperandStage.multiplierOutputTape A M H)
    (hdo : BitDFT.BankedOperandStage.dimensionTape A M H ≠
      BitDFT.BankedOperandStage.multiplierOutputTape A M H)
    (base : (BitDFT.OperandStage.control (BitDFT.CPLocal.host A M H)
      (BitDFT.BankedOperandStage.coordinateTape A M H j)
      (BitDFT.BankedOperandStage.dimensionTape A M H)
      (BitDFT.BankedOperandStage.multiplierOutputTape A M H) hc hd ho hcd hco hdo).machine.Cfg)
    (hdCells : base.cells (BitDFT.BankedOperandStage.dimensionTape A M H) =
      (BitDFT.CPLocal.host A M H).tapeOf
        (dimension.map (BitDFT.CPLocal.host A M H).bitSym))
    (hdHead : base.head (BitDFT.BankedOperandStage.dimensionTape A M H) = dimension.length + 1)
    (hcCells : base.cells (BitDFT.BankedOperandStage.coordinateTape A M H j) =
      (BitDFT.CPLocal.host A M H).tapeOf
        (([sign, high] ++ low).map (BitDFT.CPLocal.host A M H).bitSym))
    (hcHead : base.head (BitDFT.BankedOperandStage.coordinateTape A M H j) = low.length + 3)
    (hworkBase : ∀ i : Fin (M.k + 2), 2 ≤ i.val →
      base.cells (BitDFT.CPLocal.multiplierTapeRoute A M H i) =
        (BitDFT.CPLocal.host A M H).tapeOf [] ∧
      base.head (BitDFT.CPLocal.multiplierTapeRoute A M H i) = 1)
    (hpad : ∀ p, 1 ≤ p →
      ((BitDFT.CPLocal.host A M H).tapeOf
        ((BitDFT.CPLocal.host A M H).blank ::
          List.replicate low.length (BitDFT.CPLocal.host A M H).zero)) p ≠
          (BitDFT.CPLocal.host A M H).startSym)
    (hdimBlank : ((BitDFT.CPLocal.host A M H).tapeOf
      (dimension.map (BitDFT.CPLocal.host A M H).bitSym))
        (dimension.length + 1) = (BitDFT.CPLocal.host A M H).blank) :
    let N := BitDFT.CPLocal.host A M H
    let coord := BitDFT.BankedOperandStage.coordinateTape A M H j
    let dim := BitDFT.BankedOperandStage.dimensionTape A M H
    let out := BitDFT.BankedOperandStage.multiplierOutputTape A M H
    ∃ final : (BitDFT.OperandStage.control N coord dim out hc hd ho hcd hco hdo).machine.Cfg,
      (BitDFT.OperandStage.control N coord dim out hc hd ho hcd hco hdo).machine.step ^[
        2 * dimension.length + 3 * low.length + 14]
        (@BitDFT.CPLocal.entryFrame N coord dim out hc hd ho hcd hco hdo base
          ([sign, high] ++ low)) = final ∧
      final.state = BitDFT.OperandStage.State.halt ∧
      final.cells out = N.tapeOf (N.blank ::
        (List.replicate (low.length - dimension.length) N.zero ++
          dimension.map N.bitSym ++ [N.sep] ++ low.map N.bitSym)) ∧
      (∀ i : Fin (M.k + 2), 2 ≤ i.val →
        final.cells (BitDFT.CPLocal.multiplierTapeRoute A M H i) = N.tapeOf [] ∧
        final.head (BitDFT.CPLocal.multiplierTapeRoute A M H i) = 1) := by
  dsimp
  let N := BitDFT.CPLocal.host A M H
  let coord := BitDFT.BankedOperandStage.coordinateTape A M H j
  let dim := BitDFT.BankedOperandStage.dimensionTape A M H
  let out := BitDFT.BankedOperandStage.multiplierOutputTape A M H
  let P := BitDFT.OperandStage.control N coord dim out hc hd ho hcd hco hdo
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
  have hEntry : @BitDFT.CPLocal.entryFrame N coord dim out hc hd ho hcd hco hdo base
      ([sign, high] ++ low) =
      @BitDFT.BankedOperandStageProofSupport.initialStageFrame N coord dim out hc hd ho hcd hco hdo
        base ([sign, high] ++ low) := by rfl
  have hrun' : P.machine.step^[2 * dimension.length + 3 * low.length + 14]
      (@BitDFT.CPLocal.entryFrame N coord dim out hc hd ho hcd hco hdo base
        ([sign, high] ++ low)) = final := by
    rw [hEntry]
    simpa [final] using hrun
  have hstate : final.state = BitDFT.OperandStage.State.halt := by rfl
  have hout : final.cells out = N.tapeOf (N.blank ::
      (List.replicate (low.length - dimension.length) N.zero ++
        dimension.map N.bitSym ++ [N.sep] ++ low.map N.bitSym)) := by
    rw [← hrun']
    change (P.machine.step^[2 * dimension.length + 3 * low.length + 14]
      (@BitDFT.CPLocal.entryFrame N coord dim out hc hd ho hcd hco hdo base
        ([sign, high] ++ low))).cells out = _
    rw [hEntry]
    simpa [BitDFT.BankedOperandStageProofSupport.coordinateCopyFrame, hco, hdo] using hbuffer
  have hworkFinal : ∀ i : Fin (M.k + 2), 2 ≤ i.val →
      final.cells (BitDFT.CPLocal.multiplierTapeRoute A M H i) = N.tapeOf [] ∧
      final.head (BitDFT.CPLocal.multiplierTapeRoute A M H i) = 1 := by
    intro i hi
    let p := BitDFT.CPLocal.multiplierTapeRoute A M H i
    have hpVal : p.val = A.k + i.val - 1 := by
      have h := BitDFT.DedicatedTapeBanks.multiplier_work_address A
        (BitDFT.CPLocal.tracked M) H i (by omega)
      have hv := congrArg Fin.val h
      simpa [p, BitDFT.CPLocal.multiplierTapeRoute,
        BitDFT.CPLocal.tracked, BitDFT.BankedTripleAlphabetHost.route,
        BitDFT.TapeExtension.oldTape, Fin.cast] using hv
    have hpCoord : p ≠ coord := by
      intro he
      have hv := congrArg Fin.val he
      rw [hpVal] at hv
      simp [p, coord, BitDFT.CPLocal.multiplierTapeRoute,
        BitDFT.CPLocal.tracked, BitDFT.BankedOperandStage.coordinateTape] at hv
      omega
    have hpDim : p ≠ dim := by
      intro he
      have hv := congrArg Fin.val he
      rw [hpVal] at hv
      simp [p, dim, BitDFT.CPLocal.multiplierTapeRoute,
        BitDFT.CPLocal.tracked, BitDFT.BankedOperandStage.dimensionTape] at hv
      omega
    have hpOut : p ≠ out := by
      intro he
      have hv := congrArg Fin.val he
      rw [hpVal] at hv
      simp [p, out, BitDFT.CPLocal.multiplierTapeRoute,
        BitDFT.CPLocal.tracked, BitDFT.BankedOperandStage.multiplierOutputTape] at hv
      omega
    have hpres := BitDFT.OperandStage.run_preserves_other_tape (N := N)
      coord dim out hc hd ho hcd hco hdo
      (@BitDFT.CPLocal.entryFrame N coord dim out hc hd ho hcd hco hdo base
        ([sign, high] ++ low)) p hpCoord hpDim hpOut
      (2 * dimension.length + 3 * low.length + 14)
    have hentryCells :
        (@BitDFT.CPLocal.entryFrame N coord dim out hc hd ho hcd hco hdo base
          ([sign, high] ++ low)).cells p = base.cells p := by
      by_cases hpc : p = coord
      · exact (hpCoord hpc).elim
      · by_cases hpo : p = out
        · exact (hpOut hpo).elim
        · change (if p = coord then N.tapeOf (([sign, high] ++ low).map N.bitSym)
            else if p = out then N.tapeOf [] else base.cells p) = base.cells p
          simp [hpc, hpo]
    have hentryHead :
        (@BitDFT.CPLocal.entryFrame N coord dim out hc hd ho hcd hco hdo base
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
          (@BitDFT.CPLocal.entryFrame N coord dim out hc hd ho hcd hco hdo base
            ([sign, high] ++ low))).cells p := by rw [hrun']
        _ = base.cells p := hpres.1.trans hentryCells
        _ = N.tapeOf [] := hbase.1
    · calc
        final.head p = (P.machine.step^[2 * dimension.length + 3 * low.length + 14]
          (@BitDFT.CPLocal.entryFrame N coord dim out hc hd ho hcd hco hdo base
            ([sign, high] ++ low))).head p := by rw [hrun']
        _ = base.head p := hpres.2.trans hentryHead
        _ = 1 := hbase.2
  exact ⟨final, hrun', hstate, hout, hworkFinal⟩

end
