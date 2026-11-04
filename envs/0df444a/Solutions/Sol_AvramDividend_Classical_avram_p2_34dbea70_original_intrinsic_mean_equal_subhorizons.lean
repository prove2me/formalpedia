-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_34dbea70_original_intrinsic_mean_equal_subhorizons
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T16:06:51.813714+00:00
-- url     : https://prove2.me/submissions/bc9f3ae1-fc05-45eb-8fd8-403eccf3a609

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_original_intrinsic_mean_integer_multiple_horizon

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Partition the original intrinsic mean over equal-length subintervals. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (B : Set ℝ)
    (hB : MeasurableSet B) (t : ℝ≥0) (n : ℕ) (hn : n ≠ 0) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 =>
        (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 t ×ˢ B) ∂P) =
    n • (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 =>
        (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 (t / (n : ℝ≥0)) ×ˢ B) ∂P) := by
  have hcast : (n : ℝ≥0) ≠ 0 := by exact_mod_cast hn
  have htimes : n • (t / (n : ℝ≥0)) = t := by
    rw [nsmul_eq_mul]
    field_simp
  have h :=
    avram_p2_34dbea70_original_intrinsic_mean_integer_multiple_horizon
      X B hB (t / (n : ℝ≥0)) n
  rw [htimes] at h
  exact h
