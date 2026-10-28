-- Prove2me | solution 1 for AvramDividend.Classical.causal_Ioc_convolution_powers_full_real_recursion
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T19:24:59.922612+00:00
-- url     : https://prove2.me/submissions/56f09a8b-7c23-49db-a06f-4230ff47fd87

import Theorems.Thm_AvramDividend_Classical_causal_real_convolution_equals_positive_interval_under_support

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set

/-- Causal Ioc recursion preserves zero support and equals the full real
Lebesgue convolution recursion used in the corrected renewal series. -/
theorem solution
    (κ : ℝ → ℝ) (F : ℕ → ℝ → ℝ)
    (hκzero : ∀ x : ℝ, x ≤ 0 → κ x = 0)
    (hF0 : F 0 = κ)
    (hFsucc : ∀ n : ℕ, F (n + 1) =
      fun x : ℝ => ∫ y in Ioc (0 : ℝ) x,
        κ y * F n (x - y) ∂volume) :
    (∀ n : ℕ, ∀ x : ℝ, x ≤ 0 → F n x = 0) ∧
    (∀ n : ℕ, F (n + 1) =
      fun x : ℝ => ∫ y : ℝ, κ y * F n (x - y) ∂volume) := by
  have hzero : ∀ n : ℕ, ∀ x : ℝ, x ≤ 0 → F n x = 0 := by
    intro n
    induction n with
    | zero =>
        intro x hx
        rw [hF0]
        exact hκzero x hx
    | succ n ih =>
        intro x hx
        change F (n + 1) x = 0
        rw [congrFun (hFsucc n) x]
        have hs : Ioc (0 : ℝ) x = ∅ := by
          ext y
          constructor
          · intro hy
            exact False.elim ((not_lt_of_ge hx)
              (lt_of_lt_of_le hy.1 hy.2))
          · intro hy
            simp at hy
        simp [hs]
  refine ⟨hzero, ?_⟩
  intro n
  funext x
  calc
    F (n + 1) x =
        ∫ y in Ioc (0 : ℝ) x, κ y * F n (x - y) ∂volume :=
      congrFun (hFsucc n) x
    _ = ∫ y : ℝ, κ y * F n (x - y) ∂volume :=
      (causal_real_convolution_equals_positive_interval_under_support
        κ (F n) hκzero (hzero n) x).symm
