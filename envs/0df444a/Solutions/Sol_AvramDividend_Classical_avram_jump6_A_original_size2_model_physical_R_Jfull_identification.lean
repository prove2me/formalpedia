-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_A_original_size2_model_physical_R_Jfull_identification
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T08:27:19.003062+00:00
-- url     : https://prove2.me/submissions/d09da13d-a805-4882-bcf1-4c28a2ab18e6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_b27_original_intrinsic_large_only_residual_eq_gaussian
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (B N : ℝ≥0 → ℝ)
    (R Jsmall Jfull : ℝ≥0 → Ω → ℝ)
    (hc : X.c = 0)
    (hν : X.ν (Ioc (-1 : ℝ) 0) = 0)
    (hPath : ∀ t : ℝ≥0, X.X t ω = B t - 2 * N t)
    (hLarge : ∀ t : ℝ≥0,
      avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω = -2 * N t)
    (hJumps : ∀ u : ℝ≥0, 0 < u →
      (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0 ∨
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤ -1))
    (hR : ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (nhds (R t ω)))
    (hJzero : ∀ t : ℝ≥0, Jsmall t ω = 0)
    (hFull : ∀ t : ℝ≥0, Jfull t ω = Jsmall t ω +
      avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω +
        (t : ℝ) * (X.c - ∫ η, X.X 1 η ∂P))
    (hMean : (∫ η, X.X 1 η ∂P) = (-2 : ℝ)) :
    (∀ t : ℝ≥0, R t ω = B t) ∧
    (∀ t : ℝ≥0, Jfull t ω = -2 * N t + 2 * (t : ℝ)) := by
  constructor
  · intro t
    have hEq (k : ℕ) :
        avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω = B t :=
      avram_b27_original_intrinsic_large_only_residual_eq_gaussian
        X ω B N hc hν hPath hLarge hJumps k t
    have hBrown :
        Tendsto (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
            atTop (nhds (B t)) := by
      simpa only [hEq] using
        (tendsto_const_nhds :
          Tendsto (fun _ : ℕ => B t) atTop (nhds (B t)))
    exact tendsto_nhds_unique (hR t) hBrown
  · intro t
    rw [hFull t, hJzero t, hLarge t, hc, hMean]
    ring
