-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_e_compensator_finite_signed_predictable_real_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T13:06:10.690475+00:00
-- url     : https://prove2.me/submissions/e6ac2b85-e1de-462c-8441-5a503e7d875a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_signed_past_weighted_real_rate

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The genuine source marked jump measure compensates finite signed
predictable-simple rectangles in real L¹, conditional only on each source rate. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    {ι : Type*} (S : Finset ι)
    (s t : ι → ℝ≥0) (hst : ∀ i ∈ S, s i ≤ t i)
    (B : ι → Set ℝ) (hB : ∀ i ∈ S, MeasurableSet (B i))
    (Wpos Wneg : ι → Ω → ℝ≥0∞)
    (hWp : ∀ i ∈ S, Measurable[𝓕 (s i)] (Wpos i))
    (hWn : ∀ i ∈ S, Measurable[𝓕 (s i)] (Wneg i))
    (hFp : ∀ i ∈ S, (∫⁻ ω, Wpos i ω ∂P) < ⊤)
    (hFn : ∀ i ∈ S, (∫⁻ ω, Wneg i ω ∂P) < ⊤)
    (hν : ∀ i ∈ S, X.ν (B i) < ⊤)
    (hRate : ∀ i ∈ S, (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc (s i) (t i) ×ˢ B i) ∂P) =
      (((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν (B i))) :
    let J : ι → Ω → ℝ := fun i ω =>
      (Wpos i ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc (s i) (t i) ×ˢ B i)).toReal -
      (Wneg i ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc (s i) (t i) ×ˢ B i)).toReal
    let rate : ι → ℝ := fun i => (((∫⁻ ω, Wpos i ω ∂P) *
      (((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν (B i))).toReal -
    ((∫⁻ ω, Wneg i ω ∂P) *
      (((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν (B i))).toReal)
    Integrable (fun ω => ∑ i ∈ S, J i ω) P ∧
      (∫ ω, ∑ i ∈ S, J i ω ∂P) = ∑ i ∈ S, rate i := by
  dsimp only
  have hOne (i : ι) (hi : i ∈ S) :=
    avram_p2_e_compensator_signed_past_weighted_real_rate
      X (s i) (t i) (hst i hi) (B i) (hB i hi)
      (Wpos i) (Wneg i) (hWp i hi) (hWn i hi)
      (hFp i hi) (hFn i hi) (hν i hi) (hRate i hi)
  have hIntegrable (i : ι) (hi : i ∈ S) := (hOne i hi).1
  constructor
  · exact integrable_finset_sum S hIntegrable
  · rw [integral_finset_sum S hIntegrable]
    exact Finset.sum_congr rfl (fun i hi => (hOne i hi).2)
