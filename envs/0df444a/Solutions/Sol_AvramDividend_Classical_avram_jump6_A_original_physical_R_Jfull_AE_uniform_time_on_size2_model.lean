-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_A_original_physical_R_Jfull_AE_uniform_time_on_size2_model
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T15:56:51.682183+00:00
-- url     : https://prove2.me/submissions/05ce3095-9870-4f47-a655-6dcb2d73730c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_original_size2_model_physical_R_Jfull_identification
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
    (B N R Jsmall Jfull : ℝ≥0 → Ω → ℝ)
    (hc : X.c = 0)
    (hν : X.ν (Ioc (-1 : ℝ) 0) = 0)
    (hPath : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      X.X t ω = B t ω - 2 * N t ω)
    (hLarge : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω = -2 * N t ω)
    (hJumps : ∀ᵐ ω ∂P, ∀ u : ℝ≥0, 0 < u →
      (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0 ∨
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤ -1))
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (nhds (R t ω)))
    (hJzero : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, Jsmall t ω = 0)
    (hFull : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Jfull t ω = Jsmall t ω +
        avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω +
        (t : ℝ) * (X.c - ∫ η, X.X 1 η ∂P))
    (hMean : (∫ η, X.X 1 η ∂P) = (-2 : ℝ)) :
    ∀ᵐ ω ∂P,
      (∀ t : ℝ≥0, R t ω = B t ω) ∧
      (∀ t : ℝ≥0, Jfull t ω = -2 * N t ω + 2 * (t : ℝ)) := by
  filter_upwards [hPath, hLarge, hJumps, hR, hJzero, hFull]
    with ω hp hl hj hr hz hf
  exact avram_jump6_A_original_size2_model_physical_R_Jfull_identification
    X ω (fun t => B t ω) (fun t => N t ω)
    R Jsmall Jfull hc hν hp hl hj hr hz hf hMean
