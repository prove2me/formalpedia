-- Prove2me | solution 1 for BitDFT.ReaderHostFrame.reader_stage_reaches_multiplier_call
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T19:47:40.535296+00:00
-- url     : https://prove2.me/submissions/dbcbd3de-56d8-40ef-acdb-135ec503778c

import Theorems.Thm_BitDFT_staged_call_from_host_buffer
import Theorems.Thm_BitDFT_ReaderOutputStageRun_reader_outputs_stage_rewound_with_work
import Theorems.Thm_BitDFT_ReaderHostFrame_staging_output_route_is_tracked_output
import Theorems.Thm_BitDFT_ReaderHostFrame_tracked_input_word_embeds
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
open IntMul BitDFT BitDFT.ReaderHostFrame

theorem solution
    (A M H : MultitapeTM) (hH4 : 3 < H.k)
    (cF : A.Cfg) (cH : H.Cfg) (j : Fin A.k) (hj : 1 ≤ j.val)
    (dimension low : List Bool) (sign high : Bool)
    (hcoord : cF.cells j = A.tapeOf (([sign, high] ++ low).map A.bitSym))
    (hdim : cH.cells ⟨3, hH4⟩ = H.tapeOf (dimension.map H.bitSym))
    (hdimHead : cH.head ⟨3, hH4⟩ = dimension.length + 1)
    (hq : dimension.length ≤ low.length)
    (hc : BankedOperandStage.coordinateTape A M H j ≠ (host A M H).inTape)
    (hd : BankedOperandStage.dimensionTape A M H ≠ (host A M H).inTape)
    (ho : BankedOperandStage.multiplierOutputTape A M H ≠ (host A M H).inTape)
    (hcd : BankedOperandStage.coordinateTape A M H j ≠ BankedOperandStage.dimensionTape A M H)
    (hco : BankedOperandStage.coordinateTape A M H j ≠ BankedOperandStage.multiplierOutputTape A M H)
    (hdo : BankedOperandStage.dimensionTape A M H ≠ BankedOperandStage.multiplierOutputTape A M H)
    (hpad : ∀ p, 1 ≤ p →
      ((host A M H).tapeOf ((host A M H).blank ::
        List.replicate low.length (host A M H).zero)) p ≠ (host A M H).startSym)
    (hdimBlank : ((host A M H).tapeOf (dimension.map (host A M H).bitSym))
        (dimension.length + 1) = (host A M H).blank)
    (T : ℕ) (halt : (M.step^[T] (M.initCfg
        (List.replicate (low.length - dimension.length) false ++ dimension) low)).state = M.qHalt)
    (w : List Bool)
    (hout : (M.step^[T] (M.initCfg
        (List.replicate (low.length - dimension.length) false ++ dimension) low)).cells M.outTape =
          M.tapeOf (w.map M.bitSym)) :
    ∃ base : (TrackedBankedCall.machine M).Cfg, ∃ t : ℕ,
      base.state = (TrackedBankedCall.machine M).qStart ∧
      base.cells (TrackedBankedCall.machine M).outTape =
        (TrackedBankedCall.machine M).tapeOf
          ((TrackedBankedCall.machine M).blank ::
            (TrackedBankPreparation.inputWord M
              (List.replicate (low.length - dimension.length) false ++ dimension) low).map
              (fun s => some (s, true))) ∧
      base.head (TrackedBankedCall.machine M).outTape = 1 ∧
      (∀ i : Fin (M.k + 2), 2 ≤ i.val →
        base.cells i = (TrackedBankedCall.machine M).tapeOf [] ∧ base.head i = 1) ∧
      ∃ t' : ℕ,
        t' ≤ T + 5 * TrackedBankCleanup.span M
          (TrackedBankedSimulation.extents M
            (M.initCfg (List.replicate (low.length - dimension.length) false ++ dimension) low)
            (TrackedBankPreparation.initialExtent M
              (List.replicate (low.length - dimension.length) false ++ dimension) low) T) +
          2 * (TrackedBankPreparation.inputWord M
            (List.replicate (low.length - dimension.length) false ++ dimension) low).length + 13 ∧
        (TrackedBankedCall.machine M).step^[t'] base =
          TrackedBankedCall.finalFrame M base 1 (fun _ => 1)
            (TrackedBankedSimulation.extents M
              (M.initCfg (List.replicate (low.length - dimension.length) false ++ dimension) low)
              (TrackedBankPreparation.initialExtent M
                (List.replicate (low.length - dimension.length) false ++ dimension) low) T)
            (M.step^[T] (M.initCfg
              (List.replicate (low.length - dimension.length) false ++ dimension) low)) w := by
  let N := host A M H
  let coord := BankedOperandStage.coordinateTape A M H j
  let dim := BankedOperandStage.dimensionTape A M H
  let out := BankedOperandStage.multiplierOutputTape A M H
  let x := List.replicate (low.length - dimension.length) false ++ dimension
  let e0 := TripleAlphabet.multiplier A (tracked M) H
  let e : AlphabetEmbedding.Map (TrackedBankedCall.machine M) N := {
    encode := e0.encode
    blank := by
      change e0.encode (TrackedBankedCall.machine M).blank =
        (TripleAlphabet.carrier A (tracked M) H).blank
      exact e0.blank
    marker := by
      change e0.encode (TrackedBankedCall.machine M).startSym =
        (TripleAlphabet.carrier A (tracked M) H).startSym
      exact e0.marker
    zero := by
      change e0.encode (TrackedBankedCall.machine M).zero =
        (TripleAlphabet.carrier A (tracked M) H).zero
      exact e0.zero
    one := by
      change e0.encode (TrackedBankedCall.machine M).one =
        (TripleAlphabet.carrier A (tracked M) H).one
      exact e0.one
    sep := by
      change e0.encode (TrackedBankedCall.machine M).sep =
        (TripleAlphabet.carrier A (tracked M) H).sep
      exact e0.sep
  }
  obtain ⟨base0, hdim0, hdimHead0, hcoord0, hcoordHead0, hwork0,
      final, hrun, hhalt, hbuffer, v, hv, hrewindRun, hwork⟩ :=
    ReaderOutputStageRun.reader_outputs_stage_rewound_with_work A M H hH4 cF cH j hj dimension low
      sign high hcoord hdim hdimHead hq hc hd ho hcd hco hdo hpad hdimBlank
  have houtRoute : out = multiplierTapeRoute A M H (tracked M).outTape :=
    staging_output_route_is_tracked_output A M H
  have hword0 := tracked_input_word_embeds A M H x low
  have hword1 := hword0
  simp only [List.map_map, Function.comp_apply] at hword1
  have hmap : (TrackedBankPreparation.inputWord M x low).map
      (fun s => (TripleAlphabet.multiplier A (tracked M) H).encode (some (s, true))) =
      ((TrackedBankPreparation.inputWord M x low).map (fun s => some (s, true))).map
        (TripleAlphabet.multiplier A (tracked M) H).encode := by
    rw [List.map_map]
    rfl
  have hword : (TrackedBankPreparation.inputWord M x low).map
      (fun s => e.encode (some (s, true))) =
      List.replicate (low.length - dimension.length) (host A M H).zero ++
        dimension.map (host A M H).bitSym ++ [(host A M H).sep] ++
        low.map (host A M H).bitSym := by
    change (TrackedBankPreparation.inputWord M x low).map
      (fun s => e0.encode (some (s, true))) = _
    rw [hmap, tracked_input_word_embeds A M H x low]
    simp [x, List.map_append, List.map_replicate, MultitapeTM.bitSym]
    rfl
  let c : N.Cfg := ⟨N.qStart, final.cells, Function.update final.head out 1⟩
  have hbuf : c.cells (multiplierTapeRoute A M H (tracked M).outTape) =
      N.tapeOf ((TripleAlphabet.multiplier A (tracked M) H).encode
          (TrackedBankedCall.machine M).blank ::
        (TrackedBankPreparation.inputWord M x low).map
          (fun s => (TripleAlphabet.multiplier A (tracked M) H).encode (some (s, true)))) := by
    change final.cells (multiplierTapeRoute A M H (tracked M).outTape) = _
    rw [← houtRoute, hbuffer]
    change (host A M H).tapeOf ((host A M H).blank ::
      (List.replicate (low.length - dimension.length) (host A M H).zero ++
        dimension.map (host A M H).bitSym ++ [(host A M H).sep] ++
        low.map (host A M H).bitSym)) = N.tapeOf _
    have hlist : ((host A M H).blank ::
        (List.replicate (low.length - dimension.length) (host A M H).zero ++
          dimension.map (host A M H).bitSym ++ [(host A M H).sep] ++
          low.map (host A M H).bitSym)) =
        ((TrackedBankedCall.machine M).blank ::
          (TrackedBankPreparation.inputWord M x low).map
            (fun s => some (s, true))).map e.encode := by
      have hblank : N.blank = e.encode (TrackedBankedCall.machine M).blank := e.blank.symm
      rw [hblank]
      simp only [List.map_cons]
      congr 1
      exact hword.symm.trans hmap
    have henc : ((TrackedBankPreparation.inputWord M x low).map
        (fun s => some (s, true))).map e.encode =
        (TrackedBankPreparation.inputWord M x low).map
          (fun s => e.encode (some (s, true))) := by
      rw [List.map_map]
      rfl
    have hlist' :
        (host A M H).blank ::
            (List.replicate (low.length - dimension.length) (host A M H).zero ++
              dimension.map (host A M H).bitSym ++ [(host A M H).sep] ++
              low.map (host A M H).bitSym) =
          e.encode (TrackedBankedCall.machine M).blank ::
            (TrackedBankPreparation.inputWord M x low).map
              (fun s => e.encode (some (s, true))) := by
      rw [hlist, List.map_cons, henc]
    change N.tapeOf
        ((host A M H).blank ::
          (List.replicate (low.length - dimension.length) (host A M H).zero ++
            dimension.map (host A M H).bitSym ++ [(host A M H).sep] ++
            low.map (host A M H).bitSym)) =
      N.tapeOf
        (e.encode (TrackedBankedCall.machine M).blank ::
          (TrackedBankPreparation.inputWord M x low).map
            (fun s => e.encode (some (s, true))))
    rw [hlist']
  have hhead : c.head (multiplierTapeRoute A M H (tracked M).outTape) = 1 := by
    change Function.update final.head out 1 (multiplierTapeRoute A M H (tracked M).outTape) = 1
    rw [← houtRoute]
    exact Function.update_self out 1 final.head
  have hwork' : ∀ i : Fin (M.k + 2), 2 ≤ i.val →
      c.cells (multiplierTapeRoute A M H i) = N.tapeOf [] ∧
      c.head (multiplierTapeRoute A M H i) = 1 := by
    intro i hi
    have hh := hwork i hi
    exact ⟨hh.1, by simpa [c, RewindTape.frame, Function.update] using hh.2⟩
  obtain ⟨base, t, hstart, hcaller, hcallerHead, hcallerWork, htime, hrun⟩ :=
    staged_call_from_host_buffer M N e
      (multiplierTapeRoute A M H) c x low hbuf hhead hwork' T halt w hout
  exact ⟨base, t, hstart, hcaller, hcallerHead, hcallerWork,
    ⟨t, htime, hrun⟩⟩

end
