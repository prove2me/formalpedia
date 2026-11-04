-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_separated_marked_finite_simple_predictable_L1_rate
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T07:23:43.193197+00:00
-- url     : https://prove2.me/submissions/71c71807-4f81-4bd1-a0d4-6a1a92de8a27
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_separated_marked_adapted_weight_L1_rate
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_intrinsic_marked_future_measurable_extractor
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_shifted_future_path_coordinate_product_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Finite predictable simple weighted cells for the actual original Lévy jump measure. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (S : Finset ℕ) (s T : ℕ → ℝ≥0)
    (H : ℕ → Ω → ℝ≥0∞)
    (hH : ∀ i ∈ S, Measurable[𝓕 (s i)] (H i))
    (B : ℕ → Set ℝ)
    (hB : ∀ i ∈ S, MeasurableSet (B i))
    (ε : ℕ → ℝ) (hε : ∀ i ∈ S, 0 < ε i)
    (hBsep : ∀ i ∈ S, B i ⊆ Iic (-(ε i))) :
    (∫⁻ ω, ∑ i ∈ S, H i ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc (s i) (s i + T i) ×ˢ B i) ∂P) =
    ∑ i ∈ S, (∫⁻ ω, H i ω ∂P) *
      ((T i : ℝ≥0) : ℝ≥0∞) * X.ν (B i) := by
  let N : ℕ → Ω → ℝ≥0∞ := fun i ω => ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc (s i) (s i + T i) ×ˢ B i)
  have hNMeas (i : ℕ) (hi : i ∈ S) : Measurable (N i) := by
    have hst : s i ≤ s i + T i := le_add_of_nonneg_right (by positivity)
    obtain ⟨F, hF, hRep⟩ :=
      avram_wave7_01_original_intrinsic_marked_future_measurable_extractor
        X (s i) (s i + T i) hst (B i) (hB i hi)
    have hFuture := hF.comp
      (avram_wave7_01_original_shifted_future_path_coordinate_product_measurable
        X (s i))
    convert hFuture using 1
    funext ω
    exact hRep ω
  have hSummand (i : ℕ) (hi : i ∈ S) :
      Measurable (fun ω : Ω => H i ω * N i ω) := by
    have hHmeas : Measurable (H i) :=
      (hH i hi).mono (𝓕.le (s i)) le_rfl
    exact hHmeas.mul (hNMeas i hi)
  change (∫⁻ ω, ∑ i ∈ S, H i ω * N i ω ∂P) =
    ∑ i ∈ S, (∫⁻ ω, H i ω ∂P) *
      ((T i : ℝ≥0) : ℝ≥0∞) * X.ν (B i)
  rw [lintegral_finset_sum S hSummand]
  apply Finset.sum_congr rfl
  intro i hi
  change (∫⁻ ω, H i ω * N i ω ∂P) =
    (∫⁻ ω, H i ω ∂P) * ((T i : ℝ≥0) : ℝ≥0∞) * X.ν (B i)
  simpa only [mul_assoc] using
    (avram_wave7_06_original_separated_marked_adapted_weight_L1_rate
      X (s i) (T i) (H i) (hH i hi)
      (B i) (hB i hi) (ε i) (hε i hi) (hBsep i hi))
