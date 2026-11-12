-- Prove2me | solution 1 for AvramDividend.Classical.avram_chat24_original_shifted_finite_prefix_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T00:42:48.494113+00:00
-- url     : https://prove2.me/submissions/3298aedf-3ec5-49ba-b856-2dc2f31464c1

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_chat24_pre_endpoint_finite_discounted_budget
import Theorems.Thm_AvramDividend_Classical_avram_chat24_finite_cash_left_to_right_discount_error
import Theorems.Thm_AvramDividend_Classical_avram_chat24_nonnegative_discount_cell_modulus
import Theorems.Thm_AvramDividend_Classical_avram_chat24_original_shifted_pre_cell_dividend_secant
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Finset AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (x δ q : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D) (w : ℝ → ℝ)
    (hs : ContDiffOn ℝ 1 w (Ioi 0)) (hg : ∀ y > 0, 1 ≤ deriv w y)
    (hδ : 0 < δ) (hq : 0 ≤ q) (ω : Ω) (u : ℕ → ℝ≥0)
    (hu : Monotone u) (hu0 : u 0 = 0) (n : ℕ) (mesh : ℝ)
    (hwidth : ∀ i < n, (u (i + 1) : ℝ) - (u i : ℝ) ≤ mesh)
    (hstop : (u n : ℝ≥0∞) < ruinTime X x D ω) :
    let e : ℕ → ℝ := fun i => Real.exp (-(q * (u i : ℝ)))
    let U : ℕ → ℝ := fun i => riskProcess X x D (u i) ω + δ
    let Z : ℕ → ℝ := fun i => x + δ + X.X (u (i + 1)) ω - D (u i) ω
    (∑ i ∈ range n, e i * (D (u (i + 1)) ω - D (u i) ω)) + e n * w (U n) ≤
      w (x + δ) + (∑ i ∈ range n,
        ((e (i + 1) - e i) * w (U i) + e (i + 1) * (w (Z i) - w (U i)))) +
        q * mesh * D (u n) ω := by
  classical
  intro e U Z
  let d : ℕ → ℝ := fun i => D (u (i + 1)) ω - D (u i) ω
  have hd (i : ℕ) (hi : i ∈ range n) : 0 ≤ d i :=
    sub_nonneg.mpr (hD.1.1.2.1 ω (hu (Nat.le_succ i)))
  have he (i : ℕ) (hi : i ∈ range n) : e i - e (i + 1) ≤ q * mesh :=
    AvramDividend.Classical.avram_chat24_nonnegative_discount_cell_modulus q _ _ mesh hq (u i).coe_nonneg
      (by exact_mod_cast hu (Nat.le_succ i)) (hwidth i (mem_range.mp hi))
  have hc := AvramDividend.Classical.avram_chat24_finite_cash_left_to_right_discount_error (range n)
    e (fun i => e (i + 1)) d (q * mesh) hd he
  have htel (k : ℕ) : (∑ i ∈ range k, d i) = D (u k) ω - D (u 0) ω := by
    induction k with
    | zero => simp
    | succ k ih => rw [sum_range_succ, ih]; dsimp [d]; ring
  have hzero : D (u 0) ω = 0 := by rw [hu0]; exact hD.1.1.1 ω
  have hdiv (i : ℕ) (hi : i < n) : d i ≤ w (Z i) - w (U (i + 1)) :=
    AvramDividend.Classical.avram_chat24_original_shifted_pre_cell_dividend_secant X x C D hD w hs hg δ hδ ω
      (u i) (u (i + 1)) (hu (Nat.le_succ i))
      (lt_of_le_of_lt (by exact_mod_cast hu (Nat.succ_le_of_lt hi)) hstop)
  have hp := AvramDividend.Classical.avram_chat24_pre_endpoint_finite_discounted_budget n e U Z d w
    (∑ i ∈ range n, e i * d i) (q * mesh * ∑ i ∈ range n, d i)
    (fun i hi => (Real.exp_pos _).le) hdiv hc
  have hU0 : U 0 = x + δ := by
    dsimp [U, riskProcess]
    rw [hu0, X.X_zero, hD.1.1.1 ω]
    ring
  simpa only [e, hu0, NNReal.coe_zero, mul_zero, neg_zero, Real.exp_zero, one_mul,
    hU0, htel, hzero, hD.1.1.1 ω, sub_zero, d] using hp
