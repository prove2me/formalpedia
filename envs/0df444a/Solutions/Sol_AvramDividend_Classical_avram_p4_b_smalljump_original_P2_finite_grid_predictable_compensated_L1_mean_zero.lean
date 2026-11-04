-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_b_smalljump_original_P2_finite_grid_predictable_compensated_L1_mean_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T23:07:44.098054+00:00
-- url     : https://prove2.me/submissions/ac475a71-1817-4657-a211-4f4149e89220

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_P2_finite_band_bounded_predictable_compensated_mean_zero
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_finite_intensity_count_integrable_and_ae_finite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The actual original Lévy P2 raw compensation and finite marked count rates
give a finite predictable simple compensated sum of physical mean zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    {ι : Type*} (S : Finset ι)
    (s t : ι → ℝ≥0) (r : ι → ℕ → ℝ≥0)
    (hsr : ∀ i ∈ S, ∀ n, s i < r i n)
    (hrt : ∀ i ∈ S, ∀ n, r i n ≤ t i)
    (B : ι → Set ℝ) (hB : ∀ i ∈ S, MeasurableSet (B i))
    (J : ι → ℝ≥0 → ℝ≥0 → Ω → ℝ≥0∞)
    (hJsource : ∀ i a b ω, J i a b ω =
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
       (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
       (Ioc a b ×ˢ B i))
    (hShort : ∀ i ∈ S,
      Tendsto (fun n => r i n - s i) atTop (𝓝 0))
    (hLong : ∀ i ∈ S,
      Tendsto (fun n => t i - r i n) atTop (𝓝 (t i - s i)))
    (hFinite : ∀ i ∈ S, X.ν (B i) ≠ ⊤)
    (hMass : ∀ i ∈ S, ∀ A : Set Ω,
      MeasurableSet[𝓕.rightCont (s i)] A → P A ≠ ⊤)
    (hRate : ∀ i ∈ S, ∀ n, (∫⁻ ω, J i (s i) (r i n) ω ∂P) =
      ((r i n - s i : ℝ≥0) : ℝ≥0∞) * X.ν (B i))
    (hRaw : ∀ i ∈ S, ∀ (u v : ℝ≥0) (A : Set Ω), u ≤ v →
      MeasurableSet[𝓕 u] A →
      (∫⁻ ω in A, J i u v ω ∂P) =
        P A * ((v - u : ℝ≥0) : ℝ≥0∞) * X.ν (B i))
    (hJmeas : ∀ i ∈ S, Measurable (J i (s i) (t i)))
    (hFullRate : ∀ i ∈ S,
      (∫⁻ ω, J i (s i) (t i) ω ∂P) =
        ((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν (B i))
    (H : ι → Ω → ℝ) (C : ι → ℝ)
    (hH : ∀ i ∈ S,
      StronglyMeasurable[𝓕.rightCont (s i)] (H i))
    (hBound : ∀ i ∈ S, ∀ᵐ ω ∂P, ‖H i ω‖ ≤ C i) :
    (∫ ω, ∑ i ∈ S, H i ω *
      ((J i (s i) (t i) ω).toReal -
        (((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν (B i)).toReal) ∂P) = 0 := by
  let rate : ι → ℝ≥0∞ := fun i =>
    ((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν (B i)
  have hJ (i : ι) (ω : Ω) : J i (s i) (t i) ω =
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
       (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
       (Ioc (s i) (t i) ×ˢ B i) := hJsource i (s i) (t i) ω
  have hInt (i : ι) (hi : i ∈ S) :
      Integrable (fun ω => H i ω *
        ((J i (s i) (t i) ω).toReal - (rate i).toReal)) P := by
    have hm := avram_p4_b_smalljump_original_finite_intensity_count_integrable_and_ae_finite
      X (s i) (t i) (B i) (J i (s i) (t i)) (hJ i)
      (hJmeas i hi) (hFullRate i hi) (hFinite i hi)
    have hYint := hm.1.sub (integrable_const (rate i).toReal)
    have hHm : StronglyMeasurable (H i) :=
      (hH i hi).mono ((𝓕.rightCont).le (s i))
    exact hYint.bdd_mul hHm.aestronglyMeasurable (hBound i hi)
  rw [integral_finset_sum S hInt]
  apply Finset.sum_eq_zero
  intro i hi
  exact avram_p4_b_smalljump_original_P2_finite_band_bounded_predictable_compensated_mean_zero
    X (s i) (t i) (r i) (hsr i hi) (hrt i hi)
    (B i) (hB i hi) (J i) (hJsource i)
    (hShort i hi) (hLong i hi) (hFinite i hi)
    (hMass i hi) (hRate i hi) (hRaw i hi)
    (hJmeas i hi) (hFullRate i hi)
    (H i) (C i) (hH i hi) (hBound i hi)
