-- Prove2me | solution 1 for AvramDividend.Classical.avram_a20_original_negative_borel_exact_raw_second_moment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T18:52:34.565205+00:00
-- url     : https://prove2.me/submissions/1f7ee5eb-f0d6-4e35-b38f-3fa6b26306dd

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ja36_original_negative_borel_cell_factorial_moment
import Theorems.Thm_AvramDividend_Classical_avram_ja35_original_negative_borel_real_count_first_moment
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (B : Set ℝ)
    (hB : MeasurableSet B) (hNeg : B ⊆ Iio (0 : ℝ)) :
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B)
    let J : Ω → ℝ := fun ω => (N ω).toReal
    let r : ℝ := ((T : ℝ≥0∞) * X.ν B).toReal
    Integrable (fun ω => (J ω) ^ 2) P ∧
    (∫ ω, (J ω) ^ 2 ∂P) = r ^ 2 + r := by
  intro N J r
  have hFac : Integrable (fun ω => J ω * (J ω - 1)) P ∧
      (∫ ω, J ω * (J ω - 1) ∂P) = r ^ 2 := by
    simpa only [N, J, r] using
      (avram_ja36_original_negative_borel_cell_factorial_moment
        X hFinite T B hB hNeg)
  have hFirst : Integrable J P ∧ (∫ ω, J ω ∂P) = r := by
    simpa only [N, J, r] using
      (avram_ja35_original_negative_borel_real_count_first_moment
        X hFinite T B hB hNeg)
  have hPoint : (fun ω => J ω ^ 2) =
      (fun ω => J ω * (J ω - 1) + J ω) := by
    funext ω
    ring
  have hsquare : Integrable (fun ω => J ω ^ 2) P := by
    rw [hPoint]
    exact hFac.1.add hFirst.1
  refine ⟨hsquare, ?_⟩
  calc
    (∫ ω, J ω ^ 2 ∂P) =
      (∫ ω, J ω * (J ω - 1) + J ω ∂P) := by
        apply integral_congr_ae
        filter_upwards [] with ω
        ring
    _ = (∫ ω, J ω * (J ω - 1) ∂P) +
        (∫ ω, J ω ∂P) := integral_add hFac.1 hFirst.1
    _ = r ^ 2 + r := by rw [hFac.2, hFirst.2]
