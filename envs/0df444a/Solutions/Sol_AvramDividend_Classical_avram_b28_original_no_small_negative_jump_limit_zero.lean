-- Prove2me | solution 1 for AvramDividend.Classical.avram_b28_original_no_small_negative_jump_limit_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T09:53:11.722426+00:00
-- url     : https://prove2.me/submissions/d12397de-bb51-4624-982b-44515f22a77e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
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
    (hν : X.ν (Ioc (-1 : ℝ) 0) = 0)
    (hLarge : ∀ᵐ ω ∂P, ∀ u : ℝ≥0, 0 < u →
      (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0 ∨
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤ -1))
    (Jsmall : ℝ≥0 → Ω → ℝ)
    (hJsource : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X k u ω)
        atTop (𝓝 (Jsmall u ω))) :
    ∀ᵐ ω ∂P, ∀ u : ℝ≥0, Jsmall u ω = 0 := by
  filter_upwards [hLarge, hJsource] with ω hJumps hLimit
  intro u
  have hEq :
      (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X k u ω) =
      (fun _ : ℕ => (0 : ℝ)) := by
    funext k
    exact avram_b27_original_no_small_band_marks_compensator_zero
      X hν ω hJumps k u
  have hZero :
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X k u ω)
          atTop (𝓝 (0 : ℝ)) := by
    rw [hEq]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique (hLimit u) hZero
