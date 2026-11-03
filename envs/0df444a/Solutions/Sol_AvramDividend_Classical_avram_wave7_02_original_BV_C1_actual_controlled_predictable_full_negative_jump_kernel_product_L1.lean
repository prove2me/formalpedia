-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_02_original_BV_C1_actual_controlled_predictable_full_negative_jump_kernel_product_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T17:02:19.354935+00:00
-- url     : https://prove2.me/submissions/373d7f23-fdf6-449b-9bd1-cd8812b0c027

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_negative_levy_small_first_moment_large_finite_piecewise_L1_envelope
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_C1_full_negative_source_mark_discounted_piecewise_variation_envelope
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_predictable_mark_kernel_L1_from_physical_mark_envelope
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal Classical
open AvramDividend.Classical
noncomputable section

/-- The original stopped BV C1 nonlinear source-jump integrand has genuine
predictable product L1 under a positive reserve compact strip. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ)
    (q : ℝ) (hq : 0 ≤ q) (a b L R : ℝ)
    (ha : 0 < a) (ha2 : a ≤ 2) (hab : a ≤ b)
    (hL : 0 ≤ L) (hR : 0 ≤ R)
    (hLip : ∀ u ∈ Icc (a / 2) b, ∀ v ∈ Icc (a / 2) b,
      |w u - w v| ≤ L * |u - v|)
    (hWbound : ∀ v : ℝ, v ≤ b → |w v| ≤ R)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤)
    (E : Set (ℝ≥0 × Ω))
    (hEregion : ∀ p ∈ E,
      Function.leftLim (fun s : ℝ≥0 =>
        x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc a b)
    (hMass : X.ν (Iic (-a / 2)) < ⊤)
    (H : ((ℝ≥0 × Ω) × ℝ) → ℝ)
    (hH : ∀ p, H p = if p.1 ∈ E ∧ p.2 < 0 then
      Real.exp (-(q * (p.1.1 : ℝ))) *
        (w (Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1 + p.2) -
         w (Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1))
      else 0)
    (hHm : (letI : MeasurableSpace (ℝ≥0 × Ω) :=
      𝓕.rightCont.predictable;
      AEStronglyMeasurable H (μ.prod (X.ν.restrict (Iio (0 : ℝ)))))) :
    (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable;
      Integrable H (μ.prod (X.ν.restrict (Iio (0 : ℝ))))) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  let g : ℝ → ℝ := fun z => if z ≤ -a / 2 then 2 * R else L * (-z)
  have hg : Integrable g (X.ν.restrict (Iio (0 : ℝ))) :=
    avram_wave7_02_original_BV_negative_levy_small_first_moment_large_finite_piecewise_L1_envelope
      X hBV a L R ha ha2 hL hR hMass
  have hBoundAll : ∀ p : ((ℝ≥0 × Ω) × ℝ), ‖H p‖ ≤ ‖g p.2‖ := by
    intro p
    rw [hH p]
    split_ifs with hp
    · obtain ⟨hpE, hz⟩ := hp
      have hValue :=
        avram_wave7_02_original_C1_full_negative_source_mark_discounted_piecewise_variation_envelope
          X x D w q hq a b L R ha hab hL hR hLip hWbound
          p.1.2 p.1.1 (hEregion p.1 hpE) p.2 hz
      have hgpos : 0 ≤ g p.2 := by
        dsimp [g]
        split_ifs with hc
        · exact mul_nonneg (by norm_num) hR
        · exact mul_nonneg hL (neg_nonneg.mpr (le_of_lt hz))
      simpa only [Real.norm_eq_abs, abs_of_nonneg hgpos] using hValue
    · simp
  exact avram_wave7_02_original_predictable_mark_kernel_L1_from_physical_mark_envelope
    X μ hμ g hg H hHm (Filter.Eventually.of_forall hBoundAll)
