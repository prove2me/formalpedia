-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_inf15_original_two_annulus_deterministic_weight_L2_isometry
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T16:46:58.729193+00:00
-- url     : https://prove2.me/submissions/411e2819-9577-4131-9b33-692ea19e2ac7

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mix_inf16_original_two_annulus_simple_weight_L2_isometry
import Theorems.Thm_AvramDividend_Classical_avram_mixed_source13_original_physical_annulus_count_variance_exact
import Theorems.Thm_AvramDividend_Classical_avram_mix_inf15_original_adjacent_annulus_compensated_covariance_zero
import Mathlib.Topology.Order.LeftRightLim
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal NNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (n m p : ℕ) (hnm : n ≤ m) (hmp : m ≤ p)
    (a b : ℝ) :
    let B : ℕ → ℕ → Set ℝ := fun i j =>
      Ioc (-(1 / ((i : ℝ) + 1))) (-(1 / ((j : ℝ) + 1)))
    let N : ℕ → ℕ → Ω → ℝ≥0∞ := fun i j ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B i j)
    let r : ℕ → ℕ → ℝ := fun i j =>
      ((T : ℝ≥0∞) * X.ν (B i j)).toReal
    let Y : Ω → ℝ := fun ω => (N n m ω).toReal - r n m
    let Z : Ω → ℝ := fun ω => (N m p ω).toReal - r m p
    Integrable (fun ω => (a * Y ω + b * Z ω) ^ 2) P ∧
      (∫ ω, (a * Y ω + b * Z ω) ^ 2 ∂P) =
        a ^ 2 * r n m + b ^ 2 * r m p := by
  exact avram_mix_inf16_original_two_annulus_simple_weight_L2_isometry
    X T n m m p hnm (le_refl m) hmp a b
