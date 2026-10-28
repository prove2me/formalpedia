-- Prove2me | solution 1 for BitDFT.staged_call_from_host_buffer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T19:39:34.831199+00:00
-- url     : https://prove2.me/submissions/645bd955-cc3f-4996-9c2f-5a0f6c138942

import Definitions.Def_IntMul_TrackedBankedCall
import Definitions.Def_BitDFT_AlphabetEmbedding
import Theorems.Thm_BitDFT_staged_call_run
import Mathlib.Data.List.GetD
import Mathlib.Tactic

set_option autoImplicit false
open IntMul BitDFT

private theorem decode_tapeOf_encoded {X Y : MultitapeTM}
    (e : AlphabetEmbedding.Map X Y) (w : List X.Sym) :
    (fun p => AlphabetEmbedding.decode e (Y.tapeOf (w.map e.encode) p)) =
      X.tapeOf w := by
  funext p
  cases p with
  | zero =>
      change AlphabetEmbedding.decode e Y.startSym = X.startSym
      rw [← e.marker, AlphabetEmbedding.decode_encode]
  | succ p =>
      change AlphabetEmbedding.decode e ((w.map e.encode).getD p Y.blank) =
        w.getD p X.blank
      rw [← e.blank]
      rw [List.getD_map, AlphabetEmbedding.decode_encode]

/-- Decode the already-staged host output buffer and its blank work bank into
an exact caller frame for the tracked multiplier. The shared root input tape is
left as supplied by the host frame. -/
theorem project_staged_multiplier_buffer (M N : MultitapeTM)
    (e : AlphabetEmbedding.Map (TrackedBankedCall.machine M) N)
    (route : Fin (TrackedBankedCall.machine M).k → Fin N.k)
    (c : N.Cfg) (x y : List Bool)
    (hbuffer : c.cells (route (TrackedBankedCall.machine M).outTape) =
      N.tapeOf (e.encode (TrackedBankedCall.machine M).blank ::
        (TrackedBankPreparation.inputWord M x y).map
          (fun s => e.encode (some (s, true)))))
    (hhead : c.head (route (TrackedBankedCall.machine M).outTape) = 1)
    (hwork : ∀ i : Fin (M.k + 2), 2 ≤ i.val →
      c.cells (route i) = N.tapeOf [] ∧ c.head (route i) = 1) :
    ∃ base : (TrackedBankedCall.machine M).Cfg,
      base.state = (TrackedBankedCall.machine M).qStart ∧
      base.cells (TrackedBankedCall.machine M).outTape =
        (TrackedBankedCall.machine M).tapeOf
          ((TrackedBankedCall.machine M).blank ::
            (TrackedBankPreparation.inputWord M x y).map
              (fun s => some (s, true))) ∧
      base.head (TrackedBankedCall.machine M).outTape = 1 ∧
      (∀ i : Fin (M.k + 2), 2 ≤ i.val →
        base.cells i = (TrackedBankedCall.machine M).tapeOf [] ∧ base.head i = 1) := by
  let T := TrackedBankedCall.machine M
  let base : T.Cfg := {
    state := T.qStart
    cells := fun i p => AlphabetEmbedding.decode e (c.cells (route i) p)
    head := fun i => c.head (route i)
  }
  refine ⟨base, rfl, ?_, ?_, ?_⟩
  · change (fun p => AlphabetEmbedding.decode e
      (c.cells (route T.outTape) p)) = T.tapeOf
        ((T.blank :: (TrackedBankPreparation.inputWord M x y).map
          (fun s => some (s, true))))
    rw [hbuffer]
    have hlist : e.encode T.blank ::
        (TrackedBankPreparation.inputWord M x y).map
          (fun s => e.encode (some (s, true))) =
        (T.blank :: (TrackedBankPreparation.inputWord M x y).map
          (fun s => some (s, true))).map e.encode := by
      simp [List.map_map]
    rw [hlist]
    exact decode_tapeOf_encoded e
      (T.blank :: (TrackedBankPreparation.inputWord M x y).map
        (fun s => some (s, true)))
  · exact hhead
  · intro i hi
    constructor
    · change (fun p => AlphabetEmbedding.decode e (c.cells (route i) p)) = T.tapeOf []
      rw [(hwork i hi).1]
      exact decode_tapeOf_encoded e []
    · exact (hwork i hi).2

/-- Once a staged host frame has the exact multiplier output payload and its
work bank is blank, projection followed by the proved tracked-call theorem
executes the multiplier from that very payload. -/
theorem solution (M N : MultitapeTM)
    (e : AlphabetEmbedding.Map (TrackedBankedCall.machine M) N)
    (route : Fin (TrackedBankedCall.machine M).k → Fin N.k)
    (c : N.Cfg) (x y : List Bool)
    (hbuffer : c.cells (route (TrackedBankedCall.machine M).outTape) =
      N.tapeOf (e.encode (TrackedBankedCall.machine M).blank ::
        (TrackedBankPreparation.inputWord M x y).map
          (fun s => e.encode (some (s, true)))))
    (hhead : c.head (route (TrackedBankedCall.machine M).outTape) = 1)
    (hwork : ∀ i : Fin (M.k + 2), 2 ≤ i.val →
      c.cells (route i) = N.tapeOf [] ∧ c.head (route i) = 1)
    (T : ℕ) (halt : (M.step^[T] (M.initCfg x y)).state = M.qHalt)
    (w : List Bool)
    (hout : (M.step^[T] (M.initCfg x y)).cells M.outTape =
      M.tapeOf (w.map M.bitSym)) :
    ∃ base : (TrackedBankedCall.machine M).Cfg, ∃ t : ℕ,
      base.state = (TrackedBankedCall.machine M).qStart ∧
      base.cells (TrackedBankedCall.machine M).outTape =
        (TrackedBankedCall.machine M).tapeOf
          ((TrackedBankedCall.machine M).blank ::
            (TrackedBankPreparation.inputWord M x y).map
              (fun s => some (s, true))) ∧
      base.head (TrackedBankedCall.machine M).outTape = 1 ∧
      (∀ i : Fin (M.k + 2), 2 ≤ i.val →
        base.cells i = (TrackedBankedCall.machine M).tapeOf [] ∧ base.head i = 1) ∧
      t ≤ T + 5 * TrackedBankCleanup.span M
        (TrackedBankedSimulation.extents M (M.initCfg x y)
          (TrackedBankPreparation.initialExtent M x y) T) +
        2 * (TrackedBankPreparation.inputWord M x y).length + 13 ∧
      (TrackedBankedCall.machine M).step^[t] base =
        TrackedBankedCall.finalFrame M base 1 (fun _ => 1)
          (TrackedBankedSimulation.extents M (M.initCfg x y)
            (TrackedBankPreparation.initialExtent M x y) T)
          (M.step^[T] (M.initCfg x y)) w := by
  obtain ⟨base, hs, hbuf, hh, hwork'⟩ :=
    project_staged_multiplier_buffer M N e route c x y hbuffer hhead hwork
  obtain ⟨t, ht, hrun⟩ := staged_call_run M base x y hs hbuf hh hwork' T halt w hout
  exact ⟨base, t, hs, hbuf, hh, hwork', ht, hrun⟩

