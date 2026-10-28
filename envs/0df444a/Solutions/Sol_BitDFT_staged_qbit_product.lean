-- Prove2me | solution 1 for BitDFT.staged_qbit_product
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T02:50:03.906121+00:00
-- url     : https://prove2.me/submissions/1b960dc2-7bfb-4e08-94e6-6d25ee269e3c

import Theorems.Thm_IntMul_TrackedBankedCall_call_correct
import Theorems.Thm_BitDFT_child_call_with_precision
import Definitions.Def_IntMul_TrackedBankedCall
import Definitions.Def_BitDFT_Encoding

set_option autoImplicit false
open IntMul BitDFT
open IntMul.TrackedBankPreparation (inputWord initialExtent)

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

open IntMul BitDFT
open IntMul.TrackedBankPreparation (inputWord initialExtent)

private theorem head_bound (M : MultitapeTM) (x y : List Bool) (t : ℕ) :
    ∀ i, (M.step^[t] (M.initCfg x y)).head i ≤ t := by
  induction t with
  | zero => simp [MultitapeTM.initCfg]
  | succ t ih =>
      intro i
      rw [Function.iterate_succ_apply']
      simp only [MultitapeTM.step]
      split <;> have h := ih i <;> omega

private theorem extent_bound (M : MultitapeTM) (x y : List Bool) (t : ℕ) :
    ∀ i, TrackedBankedSimulation.extents M (M.initCfg x y)
        (TrackedBankPreparation.initialExtent M x y) t i ≤
      (TrackedBankPreparation.inputWord M x y).length + t := by
  induction t with
  | zero =>
      intro i
      simp only [TrackedBankedSimulation.extents, TrackedBankPreparation.initialExtent]
      split <;> omega
  | succ t ih =>
      intro i
      have he := ih i
      have hh := head_bound M x y t i
      simp only [TrackedBankedSimulation.extents, TrackedBankedSimulation.nextExtent]
      split <;> (try simp only [max_le_iff]) <;> omega

/-- The q-bit multiplier call can be executed directly from a prepared caller
buffer with a runtime bound in terms of the supplied multiplier's actual
q-bit bound. -/
theorem BitDFT.staged_qbit_product (M : MultitapeTM) (T : ℕ → ℝ)
    (hM : Multiplier M T) (q : ℕ) (hq : 1 ≤ q)
    (base : (TrackedBankedCall.machine M).Cfg) (x y : List Bool)
    (hx : x.length = q) (hy : y.length = q)
    (hs : base.state = (TrackedBankedCall.machine M).qStart)
    (hbuf : base.cells (TrackedBankedCall.machine M).outTape =
      (TrackedBankedCall.machine M).tapeOf
        ((TrackedBankedCall.machine M).blank ::
          (TrackedBankPreparation.inputWord M x y).map (fun s => some (s, true))))
    (hh : base.head (TrackedBankedCall.machine M).outTape = 1)
    (hwork : ∀ i : Fin (M.k + 2), 2 ≤ i.val →
      base.cells i = (TrackedBankedCall.machine M).tapeOf [] ∧ base.head i = 1) :
    ∃ t tm : ℕ,
      (tm : ℝ) ≤ T q ∧
      (t : ℝ) ≤ 6 * T q + 14 * q + 20 ∧
      (TrackedBankedCall.machine M).step^[t] base =
        TrackedBankedCall.finalFrame M base 1 (fun _ => 1)
          (TrackedBankedSimulation.extents M (M.initCfg x y)
            (TrackedBankPreparation.initialExtent M x y) tm)
          (M.step^[tm] (M.initCfg x y))
          (IntMul.bin (2*q) (IntMul.val x * IntMul.val y)) := by
  have hm := hM q hq
  change IntMul.MultipliesAt M q (T q) at hm
  obtain ⟨tm, htm, hout⟩ := hm x y hx hy
  rcases hout with ⟨halt, houtput⟩
  obtain ⟨t, ht, hrun⟩ := BitDFT.staged_call_run M base x y hs hbuf hh hwork
    tm halt (IntMul.bin (2*q) (IntMul.val x * IntMul.val y)) houtput
  have hspan : IntMul.TrackedBankCleanup.span M
      (TrackedBankedSimulation.extents M (M.initCfg x y)
        (TrackedBankPreparation.initialExtent M x y) tm) ≤
      (TrackedBankPreparation.inputWord M x y).length + tm :=
    Finset.sup_le fun i _ => extent_bound M x y tm i
  have hlen : (TrackedBankPreparation.inputWord M x y).length = 2*q+1 := by
    simp [TrackedBankPreparation.inputWord, hx, hy]
    omega
  rw [hlen] at hspan ht
  have htN : t ≤ 6*tm + 14*q + 20 := by omega
  have htR : (t : ℝ) ≤ 6*(tm : ℝ) + 14*(q : ℝ) + 20 := by exact_mod_cast htN
  refine ⟨t, tm, htm, ?_, hrun⟩
  have htmR : (tm : ℝ) ≤ T q := htm
  have hqR : (q : ℝ) = q := by norm_num
  rw [hqR]
  nlinarith


theorem solution (M : MultitapeTM) (T : ℕ → ℝ)
    (hM : Multiplier M T) (q : ℕ) (hq : 1 ≤ q)
    (base : (TrackedBankedCall.machine M).Cfg) (x y : List Bool)
    (hx : x.length = q) (hy : y.length = q)
    (hs : base.state = (TrackedBankedCall.machine M).qStart)
    (hbuf : base.cells (TrackedBankedCall.machine M).outTape =
      (TrackedBankedCall.machine M).tapeOf
        ((TrackedBankedCall.machine M).blank ::
          (TrackedBankPreparation.inputWord M x y).map (fun s => some (s, true))))
    (hh : base.head (TrackedBankedCall.machine M).outTape = 1)
    (hwork : ∀ i : Fin (M.k + 2), 2 ≤ i.val →
      base.cells i = (TrackedBankedCall.machine M).tapeOf [] ∧ base.head i = 1) :
    ∃ t tm : ℕ,
      (tm : ℝ) ≤ T q ∧
      (t : ℝ) ≤ 6 * T q + 14 * q + 20 ∧
      (TrackedBankedCall.machine M).step^[t] base =
        TrackedBankedCall.finalFrame M base 1 (fun _ => 1)
          (TrackedBankedSimulation.extents M (M.initCfg x y)
            (TrackedBankPreparation.initialExtent M x y) tm)
          (M.step^[tm] (M.initCfg x y))
          (IntMul.bin (2*q) (IntMul.val x * IntMul.val y)) := by
  exact BitDFT.staged_qbit_product M T hM q hq base x y hx hy hs hbuf hh hwork
