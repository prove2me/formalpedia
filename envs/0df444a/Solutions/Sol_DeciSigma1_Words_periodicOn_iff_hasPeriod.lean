-- Prove2me | solution 1 for DeciSigma1.Words.periodicOn_iff_hasPeriod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:36:22.524533+00:00
-- url     : https://prove2.me/submissions/f63d47e5-3df1-4693-8c0e-84e433d14719

module
public import Mathlib.Data.List.PeriodicityLemma
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Words_Periods

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Words
variable {α : Type*}
namespace DeciSigma1.Words
theorem _root_.solution {w : List α} {d s e : ℕ} (hse : s ≤ e) (he : e ≤ w.length) :
    PeriodicOn w d s e ↔ ((w.drop s).take (e - s)).HasPeriod d := by
  rw [List.hasPeriod_iff_getElem?]
  simp only [List.length_take, List.length_drop, List.getElem?_take, List.getElem?_drop]
  constructor
  · intro h i hi
    have h1 : i < e - s := by omega
    have h2 : i + d < e - s := by omega
    simp only [h1, h2, ite_true]
    exact h (s + i) (by omega) (by omega) |>.trans (by congr 1; omega)
  · intro h p hp hpe
    have := h (p - s) (by omega)
    have h1 : p - s < e - s := by omega
    have h2 : p - s + d < e - s := by omega
    simp only [h1, h2, ite_true] at this
    convert this using 2 <;> omega
end DeciSigma1.Words
