-- Prove2me | solution 1 for AvramDividend.Classical.avram_b27_original_large_only_R_Jsmall_source_limits
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T08:56:52.223194+00:00
-- url     : https://prove2.me/submissions/9960ed43-31af-4198-b09c-f406e746c268

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_b27_original_intrinsic_large_only_residual_eq_gaussian
import Theorems.Thm_AvramDividend_Classical_avram_b27_original_no_small_band_marks_compensator_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (B N : ℝ≥0 → Ω → ℝ)
    (hc : X.c = 0)
    (hν : X.ν (Ioc (-1 : ℝ) 0) = 0)
    (hPath : ∀ ω t, X.X t ω = B t ω - 2 * N t ω)
    (hLargeSum : ∀ ω t,
      avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω =
        -2 * N t ω)
    (hJumps : ∀ ω (u : ℝ≥0), 0 < u →
      (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0 ∨
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤ -1)) :
    (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (𝓝 (B t ω))) ∧
    (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω)
        atTop (𝓝 (0 : ℝ))) := by
  constructor
  · apply Filter.Eventually.of_forall
    intro ω t
    have hEq :
        (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω) =
        (fun _ : ℕ => B t ω) := by
      funext k
      exact avram_b27_original_intrinsic_large_only_residual_eq_gaussian
        X ω (fun u => B u ω) (fun u => N u ω)
        hc hν (hPath ω) (hLargeSum ω) (hJumps ω) k t
    rw [hEq]
    exact tendsto_const_nhds
  · apply Filter.Eventually.of_forall
    intro ω t
    have hEq :
        (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω) =
        (fun _ : ℕ => (0 : ℝ)) := by
      funext k
      exact avram_b27_original_no_small_band_marks_compensator_zero
        X hν ω (hJumps ω) k t
    rw [hEq]
    exact tendsto_const_nhds
