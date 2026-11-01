-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04b_actual_time_probability_controlled_gradient_MemLp_two
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T22:26:36.391862+00:00
-- url     : https://prove2.me/submissions/29500ad5-15df-463a-a276-a606312ead8c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_original_finite_horizon_controlled_gradient_actual_product_L2

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (a b u v : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo a b))
    (hau : a < u) (huv : u ≤ v) (hvb : v < b)
    (T : ℝ≥0) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let G : ℝ≥0 × Ω → ℝ := fun p =>
      if Y p ∈ Icc u v then deriv w (Y p) else 0
    MemLp G 2 ((((volume : Measure ℝ).restrict
      (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) := by
  dsimp only
  classical
  let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
    (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
  let G : ℝ≥0 × Ω → ℝ := fun p =>
    if Y p ∈ Icc u v then deriv w (Y p) else 0
  let ξ : Measure (ℝ≥0 × Ω) :=
    (((volume : Measure ℝ).restrict
      (Icc 0 (T : ℝ))).map Real.toNNReal).prod P
  change MemLp G 2 ξ
  have hsource :=
    avram_wave4_04b_original_finite_horizon_controlled_gradient_actual_product_L2
      X x D hD w a b u v hw hau huv hvb T
  have hpred : 𝓕.rightCont.predictable ≤
      (inferInstance : MeasurableSpace (ℝ≥0 × Ω)) := by
    apply MeasureTheory.measurableSpace_le_predictable_of_measurableSet
    · intro A hA
      exact (measurableSet_singleton (⊥ : ℝ≥0)).prod ((𝓕.rightCont.le ⊥) A hA)
    · intro i A hA
      exact (measurableSet_Ioi).prod ((𝓕.rightCont.le i) A hA)
  have hmeas : Measurable G :=
    hsource.1.mono hpred le_rfl
  have henergy :
      (∫⁻ p : ℝ≥0 × Ω, ENNReal.ofReal ((G p) ^ 2) ∂ξ) < ⊤ :=
    hsource.2
  have hSq : Integrable (fun p : ℝ≥0 × Ω => G p ^ 2) ξ := by
    refine ⟨(hmeas.pow_const 2).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall (fun p : ℝ≥0 × Ω => sq_nonneg (G p)))]
    exact henergy
  exact (memLp_two_iff_integrable_sq hmeas.aestronglyMeasurable).2 hSq
