-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_34dbea70_original_intrinsic_mean_integer_multiple_horizon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T15:54:27.971929+00:00
-- url     : https://prove2.me/submissions/07de6409-04ff-4c93-a964-fa33fa7b7682

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_original_marked_mean_additive_horizon_no_hypothesis

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Stationarity makes the intrinsic count mean additive over integer multiples. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (B : Set ℝ)
    (hB : MeasurableSet B) (t : ℝ≥0) (n : ℕ) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 =>
        (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 (n • t) ×ˢ B) ∂P) =
    n • (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 =>
        (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 t ×ˢ B) ∂P) := by
  let F : ℝ≥0 → ℝ≥0∞ := fun s =>
    ∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 =>
        (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 s ×ˢ B) ∂P
  change F (n • t) = n • F t
  have hzero : F 0 = 0 := by simp [F]
  have hadd (s r : ℝ≥0) : F (s + r) = F s + F r :=
    avram_p2_34dbea70_original_marked_mean_additive_horizon_no_hypothesis
      X s r B hB
  induction n with
  | zero => simpa using hzero
  | succ k ih =>
      calc
        F ((k + 1) • t) = F (k • t + t) := by rw [succ_nsmul]
        _ = F (k • t) + F t := hadd _ _
        _ = k • F t + F t := by rw [ih]
        _ = (k + 1) • F t := by rw [succ_nsmul]
