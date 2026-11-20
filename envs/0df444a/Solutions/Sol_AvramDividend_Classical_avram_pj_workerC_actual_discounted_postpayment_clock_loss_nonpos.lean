-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_workerC_actual_discounted_postpayment_clock_loss_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T22:15:48.842889+00:00
-- url     : https://prove2.me/submissions/2f5de065-e851-4ac5-b4ba-64117cc612f4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_bv_postpayment_terminal_nonnegative_separate_gradient
import Theorems.Thm_AvramDividend_Classical_capped_postPaymentReserve_ofReal_le_cap
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_positive_caplinear_extension_eq_w_closed_cap
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_bv_caplinear_postpayment_candidate_nonnegative
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (hx : 0 ≤ x) (C : ℝ≥0∞)
    (hC : 0 < C) (hxc : ENNReal.ofReal x ≤ C)
    (w V : ℝ → ℝ)
    (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ z : ℝ, z < 0 → w z = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q)
    (u : ℕ → ℝ≥0) (hu : Monotone u)
    (m : ℕ) (ω : Ω) :
    (∑ i ∈ Finset.range m,
      (Real.exp (-(q * (u (i + 1) : ℝ))) -
        Real.exp (-(q * (u i : ℝ)))) *
        V (x + X.X (u (i + 1)) ω -
          rightLimit D (u (i + 1)) ω)) ≤ 0 := by 
  classical
  apply Finset.sum_nonpos
  intro i hi
  have hTimes : (u i : ℝ) ≤ (u (i + 1) : ℝ) := by
    exact_mod_cast hu (Nat.le_succ i)
  have hExp : Real.exp (-(q * (u (i + 1) : ℝ))) ≤
      Real.exp (-(q * (u i : ℝ))) := by
    apply Real.exp_le_exp.mpr
    have hMul : q * (u i : ℝ) ≤ q * (u (i + 1) : ℝ) :=
      mul_le_mul_of_nonneg_left hTimes hq
    linarith
  have hNonneg :
      0 ≤ V (x + X.X (u (i + 1)) ω -
        rightLimit D (u (i + 1)) ω) :=
    avram_wave5_03_original_bv_caplinear_postpayment_candidate_nonnegative
      X w V C hC hw0 hw_cont hw_neg hw_smooth hw_grad
      hVtop hVfinite x hx hxc D hD ω (u (i + 1))
  exact mul_nonpos_of_nonpos_of_nonneg
    (sub_nonpos.mpr hExp) hNonneg
