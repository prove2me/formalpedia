-- Prove2me | solution 1 for Disjunctive.MonoidalStrengthening.lopsided_cut_weak_form
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T22:52:34.141767+00:00
-- url     : https://prove2.me/submissions/b88bcbf1-725b-461d-a353-d278bf3925be

import Mathlib
import Definitions.Def_Disjunctive_MonoidalStrengthening_Basic

open Disjunctive.MonoidalStrengthening in
theorem solution : ¬ (∀ {q n : ℕ} [Nonempty (Fin q)]
    (a : Fin q → Fin n → ℝ) (a0 b : Fin q → ℝ) (J1 : Finset (Fin n)) (k : Fin q)
    (ha0 : ∀ i, 0 < a0 i)
    (x : Fin n → ℝ) (hx_nonneg : 0 ≤ x) (hx_int : ∀ j ∈ J1, ∃ m : ℤ, x j = (m : ℝ))
    (hx_lb : ∀ i, b i ≤ ∑ j, a i j * x j)
    (hx_disj : ∃ i, a0 i ≤ ∑ j, a i j * x j),
    1 ≤ ∑ j ∈ J1, min ((a k j + a0 k - b k) / a0 k) (BetaJUnstrengthened a a0 j) * x j +
      ∑ j ∈ Finset.univ \ J1, BetaJUnstrengthened a a0 j * x j) := by
  intro h
  have H := @h 1 1 inferInstance (fun _ _ => 1) (fun _ => 1) (fun _ => 3) Finset.univ 0
    (fun _ => one_pos) (fun _ => 3)
    (fun _ => by norm_num)
    (fun _ _ => ⟨3, by norm_num⟩)
    (fun _ => by norm_num)
    ⟨0, by norm_num⟩
  simp only [Finset.sdiff_self, Finset.sum_empty, add_zero, Fin.sum_univ_one] at H
  have hmin : min (((1 : ℝ) + 1 - 3) / 1)
      (@BetaJUnstrengthened 1 1 inferInstance (fun _ _ => (1 : ℝ)) (fun _ => (1 : ℝ)) (0 : Fin 1)) ≤ -1 := by
    refine (min_le_left _ _).trans ?_
    norm_num
  nlinarith
