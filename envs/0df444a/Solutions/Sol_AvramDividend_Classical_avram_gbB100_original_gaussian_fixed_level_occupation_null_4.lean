-- Prove2me | solution 4 for AvramDividend.Classical.avram_gbB100_original_gaussian_fixed_level_occupation_null
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T22:44:47.531142+00:00
-- url     : https://prove2.me/submissions/7b0cdc86-35ca-466e-9ffd-4f9dac77a565
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB272_original_gaussian_fixed_level_product_measure_null
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB269_original_postpayment_reserve_joint_time_sample_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original null product-measure occupation implies exact B100 at any random horizon. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0)
    (x b : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (n : ℕ) (ρ : Ω → ℝ≥0) :
    ∀ᵐ ω ∂P,
      volume {t : ℝ |
        0 < t ∧ t < (n : ℝ) ∧ t < (ρ ω : ℝ) ∧
        x + X.X (Real.toNNReal t) ω -
          rightLimit D (Real.toNNReal t) ω = b} = 0 := by
  have hprod := avram_gbB272_original_gaussian_fixed_level_product_measure_null X hBV hν x b D hD n
  let S : Set (Ω × ℝ) := {z |
    0 < z.2 ∧ z.2 < (n : ℝ) ∧
      x + X.X (Real.toNNReal z.2) z.1 -
        rightLimit D (Real.toNNReal z.2) z.1 = b}
  have hJoint :=
    avram_gbB269_original_postpayment_reserve_joint_time_sample_measurable
      X x D hD
  have hPair : Measurable
      (fun z : Ω × ℝ => (Real.toNNReal z.2, z.1)) :=
    (measurable_real_toNNReal.comp measurable_snd).prodMk measurable_fst
  have hF : Measurable
      (fun z : Ω × ℝ => x + X.X (Real.toNNReal z.2) z.1 -
        rightLimit D (Real.toNNReal z.2) z.1) := hJoint.comp hPair
  have hS : MeasurableSet S :=
    (measurableSet_lt measurable_const measurable_snd).inter
      ((measurableSet_lt measurable_snd measurable_const).inter
        (measurableSet_eq_fun hF measurable_const))
  have hZero : (fun ω => volume (Prod.mk ω ⁻¹' S)) =ᵐ[P] 0 :=
    (Measure.measure_prod_null hS).mp hprod
  filter_upwards [hZero] with ω hω
  have hsub : {t : ℝ |
        0 < t ∧ t < (n : ℝ) ∧ t < (ρ ω : ℝ) ∧
        x + X.X (Real.toNNReal t) ω -
          rightLimit D (Real.toNNReal t) ω = b} ⊆
      (Prod.mk ω ⁻¹' S) := by
    rintro t ⟨ht0, htn, htrho, htEq⟩
    exact ⟨ht0, htn, htEq⟩
  have hle : volume {t : ℝ |
        0 < t ∧ t < (n : ℝ) ∧ t < (ρ ω : ℝ) ∧
        x + X.X (Real.toNNReal t) ω -
          rightLimit D (Real.toNNReal t) ω = b} ≤
      volume (Prod.mk ω ⁻¹' S) := measure_mono hsub
  have hle0 : volume {t : ℝ |
        0 < t ∧ t < (n : ℝ) ∧ t < (ρ ω : ℝ) ∧
        x + X.X (Real.toNNReal t) ω -
          rightLimit D (Real.toNNReal t) ω = b} ≤ 0 := by
    exact hle.trans_eq hω
  exact le_antisymm hle0 bot_le
