-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_bv_original_live_postpayment_discount_debits_nonpositive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T23:23:33.4402+00:00
-- url     : https://prove2.me/submissions/67c907a7-0fe0-486e-8711-edee66815735

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_allcap_linear_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_preruin_postpayment_nonnegative

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/- Every physical postpayment source discount decrement is nonpositive
   while its actual original clock is zero or strictly before ruin. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw0 : 0 ≤ w 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (q : ℝ) (hq : 0 ≤ q)
    (ω : Ω) (u : ℕ → ℝ≥0) (n : ℕ)
    (hu : Monotone u)
    (hPre : ∀ i : ℕ, i < n →
      u (i + 1) = 0 ∨
        (u (i + 1) : ℝ≥0∞) < ruinTime X x D ω) :
    (∑ i ∈ Finset.range n,
      (Real.exp (-(q * (u (i + 1) : ℝ))) -
        Real.exp (-(q * (u i : ℝ)))) *
      (if C = ⊤ then
        w (x + X.X (u (i + 1)) ω - rightLimit D (u (i + 1)) ω)
       else if x + X.X (u (i + 1)) ω - rightLimit D (u (i + 1)) ω ≤ C.toReal
       then w (x + X.X (u (i + 1)) ω - rightLimit D (u (i + 1)) ω)
       else w C.toReal +
         ((x + X.X (u (i + 1)) ω - rightLimit D (u (i + 1)) ω) - C.toReal))) ≤ 0 := by
  apply Finset.sum_nonpos
  intro i hi
  have hClock := hu (Nat.le_succ i)
  have hReal : (u i : ℝ) ≤ (u (i + 1) : ℝ) := by exact_mod_cast hClock
  have hExpo : Real.exp (-(q * (u (i + 1) : ℝ))) ≤
      Real.exp (-(q * (u i : ℝ))) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hReal hq]
  have hReserve := avram_p4_e_localise_preruin_postpayment_nonnegative
    X x C D hD ω (u (i + 1)) (hPre i (Finset.mem_range.mp hi))
  have hValue := avram_p3_bv_allcap_linear_nonnegative
    C hC w hw_cont hw0 hw_smooth hw_grad
    (x + X.X (u (i + 1)) ω - rightLimit D (u (i + 1)) ω) hReserve
  exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hExpo) hValue
