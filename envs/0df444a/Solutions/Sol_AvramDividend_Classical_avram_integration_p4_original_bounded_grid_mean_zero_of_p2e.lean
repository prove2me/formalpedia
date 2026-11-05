-- Prove2me | solution 1 for AvramDividend.Classical.avram_integration_p4_original_bounded_grid_mean_zero_of_p2e
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T09:53:08.785955+00:00
-- url     : https://prove2.me/submissions/a722e7a2-9307-4328-b93e-0c0d5e869ffb

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_source_intrinsic_jump_count_predictable_rectangle_compensator
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_P2_finite_grid_predictable_compensated_L1_mean_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

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
  have hRaw (i : ι) (hi : i ∈ S) (u v : ℝ≥0)
      (A : Set Ω) (huv : u ≤ v)
      (hA : MeasurableSet[𝓕 u] A) :
      (∫⁻ ω in A, J i u v ω ∂P) =
        P A * ((v - u : ℝ≥0) : ℝ≥0∞) * X.ν (B i) := by
    simpa only [hJsource] using
      (avram_wave4_04_source_intrinsic_jump_count_predictable_rectangle_compensator
        X u v huv A hA (B i) (hB i hi))
  exact avram_p4_b_smalljump_original_P2_finite_grid_predictable_compensated_L1_mean_zero
    X S s t r hsr hrt B hB J hJsource hShort hLong hFinite
    hMass hRate hRaw hJmeas hFullRate H C hH hBound
