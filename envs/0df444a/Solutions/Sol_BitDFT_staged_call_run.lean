-- Prove2me | solution 1 for BitDFT.staged_call_run
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T02:44:18.216131+00:00
-- url     : https://prove2.me/submissions/2ca295a8-855d-474e-a333-11b3092e5d43

import Theorems.Thm_IntMul_TrackedBankedCall_call_correct
import Theorems.Thm_BitDFT_child_call_with_precision

set_option autoImplicit false
open IntMul

namespace BitDFT

private theorem cfg_ext {M : MultitapeTM} (c d : M.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem staged_tagged_getD (M : MultitapeTM) (w : List M.Sym) (p : ℕ) :
    (w.map (fun a => some (a, true))).getD p (some (M.blank, false)) =
      some (w.getD p M.blank, decide (p < w.length)) := by
  by_cases hp : p < w.length
  · rw [List.getD_eq_getElem _ _ (by simpa using hp), List.getD_eq_getElem _ _ hp]
    simp [hp]
  · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hp),
      List.getD_eq_default _ _ (Nat.le_of_not_gt hp)]
    simp [hp]

private theorem staged_source_tape (M : MultitapeTM)
    (base : ℕ → TrackedBankedSimulation.Sym M) (hbase : base 0 = none)
    (w : List M.Sym) :
    TrackedBankPreparation.sourceTape M base 1 w =
      (TrackedBankPreparation.machine M).tapeOf
        (some (M.blank, false) :: w.map (fun a => some (a, true))) := by
  funext p
  cases p with
  | zero => simp [TrackedBankPreparation.sourceTape, MultitapeTM.tapeOf, hbase]
  | succ p =>
    cases p with
    | zero => simp [TrackedBankPreparation.sourceTape, MultitapeTM.tapeOf]
    | succ p =>
      simpa [TrackedBankPreparation.sourceTape, MultitapeTM.tapeOf] using
        (staged_tagged_getD M w p).symm

/-- If the caller buffer already contains the two operands in the banked
    caller's input layout, the bank-preparation phase is exactly the identity.
    This lets a parent stage a fresh operand pair between multiplier calls. -/
theorem staged_initial_frame (M : MultitapeTM)
    (base : (TrackedBankedCall.machine M).Cfg) (x y : List Bool)
    (hs : base.state = (TrackedBankedCall.machine M).qStart)
    (hbuf : base.cells (TrackedBankedCall.machine M).outTape =
      (TrackedBankedCall.machine M).tapeOf
        ((TrackedBankedCall.machine M).blank ::
          (TrackedBankPreparation.inputWord M x y).map
            (fun s => some (s, true))))
    (hh : base.head (TrackedBankedCall.machine M).outTape = 1)
    (hwork : ∀ i : Fin (M.k + 2), 2 ≤ i.val →
      base.cells i = (TrackedBankedCall.machine M).tapeOf [] ∧ base.head i = 1) :
    TrackedBankedCall.initialFrame M base 1 (fun _ => 1) x y = base := by
  apply cfg_ext
  · exact hs.symm
  · funext i
    by_cases hi : 2 ≤ i.val
    · simp only [TrackedBankedCall.initialFrame, TrackedBankedCall.liftPreparation,
        TrackedBankPreparation.initialFrame, hi, dite_true,
        TrackedBankedCall.preparationBase]
      change TrackedBankPreparation.freshTape M (base.cells i) 1 = base.cells i
      have hzero : base.cells i 0 = none := by
        rw [(hwork i hi).1]
        rfl
      rw [(hwork i hi).1]
      funext p
      cases p <;> rfl
    · have hz : i.val = 0 ∨ i.val = 1 := by omega
      rcases hz with hz | hz
      · have he : i = ⟨0, by omega⟩ := Fin.ext hz
        rw [he]
        rfl
      · have he : i = (TrackedBankedCall.machine M).outTape := Fin.ext hz
        rw [he]
        change TrackedBankPreparation.sourceTape M
          (base.cells (TrackedBankedCall.machine M).outTape) 1
          (TrackedBankPreparation.inputWord M x y) =
          base.cells (TrackedBankedCall.machine M).outTape
        have hzero : base.cells (TrackedBankedCall.machine M).outTape 0 = none := by
          rw [hbuf]
          rfl
        rw [staged_source_tape M
          (base.cells (TrackedBankedCall.machine M).outTape) hzero]
        exact hbuf.symm
  · funext i
    by_cases hi : 2 ≤ i.val
    · simp only [TrackedBankedCall.initialFrame, TrackedBankedCall.liftPreparation,
        TrackedBankPreparation.initialFrame, hi, dite_true]
      exact (hwork i hi).2.symm
    · have hz : i.val = 0 ∨ i.val = 1 := by omega
      rcases hz with hz | hz
      · have he : i = ⟨0, by omega⟩ := Fin.ext hz
        rw [he]
        rfl
      · have he : i = (TrackedBankedCall.machine M).outTape := Fin.ext hz
        rw [he]
        exact hh.symm

/-- One full multiplier call can start directly from a caller buffer containing
    the staged operand pair. All child simulation, output return, and bank
    cleanup steps are charged by the existing tracked-call theorem. -/
theorem staged_call_run (M : MultitapeTM)
    (base : (TrackedBankedCall.machine M).Cfg) (x y : List Bool)
    (hs : base.state = (TrackedBankedCall.machine M).qStart)
    (hbuf : base.cells (TrackedBankedCall.machine M).outTape =
      (TrackedBankedCall.machine M).tapeOf
        ((TrackedBankedCall.machine M).blank ::
          (TrackedBankPreparation.inputWord M x y).map
            (fun s => some (s, true))))
    (hh : base.head (TrackedBankedCall.machine M).outTape = 1)
    (hwork : ∀ i : Fin (M.k + 2), 2 ≤ i.val →
      base.cells i = (TrackedBankedCall.machine M).tapeOf [] ∧ base.head i = 1)
    (T : ℕ) (halt : (M.step^[T] (M.initCfg x y)).state = M.qHalt)
    (w : List Bool)
    (hout : (M.step^[T] (M.initCfg x y)).cells M.outTape = M.tapeOf (w.map M.bitSym)) :
    ∃ t : ℕ, t ≤ T + 5 * IntMul.TrackedBankCleanup.span M
        (IntMul.TrackedBankedSimulation.extents M (M.initCfg x y)
          (IntMul.TrackedBankPreparation.initialExtent M x y) T) +
        2 * (IntMul.TrackedBankPreparation.inputWord M x y).length + 13 ∧
      (TrackedBankedCall.machine M).step^[t] base =
        TrackedBankedCall.finalFrame M base 1 (fun _ => 1)
          (IntMul.TrackedBankedSimulation.extents M (M.initCfg x y)
            (IntMul.TrackedBankPreparation.initialExtent M x y) T)
          (M.step^[T] (M.initCfg x y)) w := by
  obtain ⟨t, ht, hr⟩ := TrackedBankedCall.call_correct M base 1
    (fun _ => 1) (by intro j; omega) x y T halt w hout
  refine ⟨t, ht, ?_⟩
  rw [staged_initial_frame M base x y hs hbuf hh hwork] at hr
  exact hr

end BitDFT

open IntMul

theorem solution (M : MultitapeTM)
    (base : (TrackedBankedCall.machine M).Cfg) (x y : List Bool)
    (hs : base.state = (TrackedBankedCall.machine M).qStart)
    (hbuf : base.cells (TrackedBankedCall.machine M).outTape =
      (TrackedBankedCall.machine M).tapeOf
        ((TrackedBankedCall.machine M).blank ::
          (TrackedBankPreparation.inputWord M x y).map
            (fun s => some (s, true))))
    (hh : base.head (TrackedBankedCall.machine M).outTape = 1)
    (hwork : ∀ i : Fin (M.k + 2), 2 ≤ i.val →
      base.cells i = (TrackedBankedCall.machine M).tapeOf [] ∧ base.head i = 1)
    (T : ℕ) (halt : (M.step^[T] (M.initCfg x y)).state = M.qHalt)
    (w : List Bool)
    (hout : (M.step^[T] (M.initCfg x y)).cells M.outTape = M.tapeOf (w.map M.bitSym)) :
    ∃ t : ℕ, t ≤ T + 5 * IntMul.TrackedBankCleanup.span M
        (IntMul.TrackedBankedSimulation.extents M (M.initCfg x y)
          (IntMul.TrackedBankPreparation.initialExtent M x y) T) +
        2 * (IntMul.TrackedBankPreparation.inputWord M x y).length + 13 ∧
      (TrackedBankedCall.machine M).step^[t] base =
        TrackedBankedCall.finalFrame M base 1 (fun _ => 1)
          (IntMul.TrackedBankedSimulation.extents M (M.initCfg x y)
            (IntMul.TrackedBankPreparation.initialExtent M x y) T)
          (M.step^[T] (M.initCfg x y)) w := by
  exact BitDFT.staged_call_run M base x y hs hbuf hh hwork T halt w hout
