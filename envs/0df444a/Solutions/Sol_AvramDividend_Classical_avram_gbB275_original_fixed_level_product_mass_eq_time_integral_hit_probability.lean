-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB275_original_fixed_level_product_mass_eq_time_integral_hit_probability
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T22:49:32.029789+00:00
-- url     : https://prove2.me/submissions/b3b54eb4-3b64-4fcc-bf41-bb668f74238b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB269_original_postpayment_reserve_joint_time_sample_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original probability-time product mass equals the time integral of fixed-level hit probabilities. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x b : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (n : ℕ) :
    (P.prod volume)
      {z : Ω × ℝ |
        0 < z.2 ∧ z.2 < (n : ℝ) ∧
        x + X.X (Real.toNNReal z.2) z.1 -
          rightLimit D (Real.toNNReal z.2) z.1 = b} =
    ∫⁻ t : ℝ, P {ω : Ω |
      0 < t ∧ t < (n : ℝ) ∧
      x + X.X (Real.toNNReal t) ω -
        rightLimit D (Real.toNNReal t) ω = b} ∂volume := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hJoint :=
    avram_gbB269_original_postpayment_reserve_joint_time_sample_measurable
      X x D hD
  have hPair : Measurable
      (fun z : Ω × ℝ => (Real.toNNReal z.2, z.1)) :=
    (measurable_real_toNNReal.comp measurable_snd).prodMk measurable_fst
  have hF : Measurable
      (fun z : Ω × ℝ => x + X.X (Real.toNNReal z.2) z.1 -
        rightLimit D (Real.toNNReal z.2) z.1) := hJoint.comp hPair
  have hS : MeasurableSet {z : Ω × ℝ |
        0 < z.2 ∧ z.2 < (n : ℝ) ∧
        x + X.X (Real.toNNReal z.2) z.1 -
          rightLimit D (Real.toNNReal z.2) z.1 = b} :=
    (measurableSet_lt measurable_const measurable_snd).inter
      ((measurableSet_lt measurable_snd measurable_const).inter
        (measurableSet_eq_fun hF measurable_const))
  have hProd :
      (P.prod volume)
        {z : Ω × ℝ |
          0 < z.2 ∧ z.2 < (n : ℝ) ∧
          x + X.X (Real.toNNReal z.2) z.1 -
            rightLimit D (Real.toNNReal z.2) z.1 = b} =
      ∫⁻ t : ℝ, P ((fun ω : Ω => (ω, t)) ⁻¹'
        {z : Ω × ℝ |
          0 < z.2 ∧ z.2 < (n : ℝ) ∧
          x + X.X (Real.toNNReal z.2) z.1 -
            rightLimit D (Real.toNNReal z.2) z.1 = b}) ∂volume := by
    exact Measure.prod_apply_symm hS
  calc
    _ = ∫⁻ t : ℝ, P ((fun ω : Ω => (ω, t)) ⁻¹'
        {z : Ω × ℝ |
          0 < z.2 ∧ z.2 < (n : ℝ) ∧
          x + X.X (Real.toNNReal z.2) z.1 -
            rightLimit D (Real.toNNReal z.2) z.1 = b}) ∂volume := hProd
    _ = _ := by
      congr 1
