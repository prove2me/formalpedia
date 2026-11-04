-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_e_compensator_finite_past_weighted_real_factor_sum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T13:06:14.208272+00:00
-- url     : https://prove2.me/submissions/d710bdbd-23fa-4f6a-b2be-77139dae0f10

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_finite_mean_past_weighted_real_integrable
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_finite_mean_past_weighted_real_factor

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Finite original predictable past-weighted jump counts have real first
moments determined by the count means alone, without any Levy ν-rate premise. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    {ι : Type*} (S : Finset ι)
    (s t : ι → ℝ≥0) (hst : ∀ i ∈ S, s i ≤ t i)
    (B : ι → Set ℝ) (hB : ∀ i ∈ S, MeasurableSet (B i))
    (W : ι → Ω → ℝ≥0∞)
    (hW : ∀ i ∈ S, Measurable[𝓕 (s i)] (W i))
    (hWfinite : ∀ i ∈ S, (∫⁻ ω, W i ω ∂P) < ⊤)
    (hNfinite : ∀ i ∈ S, (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc (s i) (t i) ×ˢ B i) ∂P) < ⊤) :
    let J : ι → Ω → ℝ := fun i ω => (W i ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc (s i) (t i) ×ˢ B i)).toReal
    let rate : ι → ℝ := fun i =>
      ((∫⁻ ω, W i ω ∂P) * (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc (s i) (t i) ×ˢ B i) ∂P)).toReal
    Integrable (fun ω => ∑ i ∈ S, J i ω) P ∧
      (∫ ω, ∑ i ∈ S, J i ω ∂P) = ∑ i ∈ S, rate i := by
  dsimp only
  have hIntegrable (i : ι) (hi : i ∈ S) :=
    avram_p2_e_compensator_finite_mean_past_weighted_real_integrable
      X (s i) (t i) (hst i hi) (B i) (hB i hi)
      (W i) (hW i hi) (hWfinite i hi) (hNfinite i hi)
  have hMean (i : ι) (hi : i ∈ S) :=
    avram_p2_e_compensator_finite_mean_past_weighted_real_factor
      X (s i) (t i) (hst i hi) (B i) (hB i hi)
      (W i) (hW i hi) (hWfinite i hi) (hNfinite i hi)
  constructor
  · exact integrable_finset_sum S hIntegrable
  · rw [integral_finset_sum S hIntegrable]
    exact Finset.sum_congr rfl (fun i hi => hMean i hi)
