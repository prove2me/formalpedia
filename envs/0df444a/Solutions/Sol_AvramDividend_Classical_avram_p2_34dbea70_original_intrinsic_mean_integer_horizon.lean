-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_34dbea70_original_intrinsic_mean_integer_horizon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T15:41:49.402347+00:00
-- url     : https://prove2.me/submissions/414aed54-0590-459d-9672-eb8cf584e02f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_original_marked_mean_additive_horizon_no_hypothesis

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Exact integer-time scaling of the original intrinsic marked jump-count mean. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (B : Set ℝ)
    (hB : MeasurableSet B) (n : ℕ) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 =>
        (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 (n : ℝ≥0) ×ˢ B) ∂P) =
    n • (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 =>
        (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 (1 : ℝ≥0) ×ˢ B) ∂P) := by
  let F : ℝ≥0 → ℝ≥0∞ := fun T =>
    ∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 =>
        (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ B) ∂P
  change F n = n • F 1
  have hzero : F 0 = 0 := by simp [F]
  have hadd (s t : ℝ≥0) : F (s + t) = F s + F t :=
    avram_p2_34dbea70_original_marked_mean_additive_horizon_no_hypothesis
      X s t B hB
  induction n with
  | zero => simpa using hzero
  | succ k ih =>
      have hcast : ((k + 1 : ℕ) : ℝ≥0) = (k : ℝ≥0) + 1 := by push_cast; rfl
      rw [hcast, hadd, ih, succ_nsmul]
