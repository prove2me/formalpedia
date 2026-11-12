-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18s_original_J_zero_origin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T10:47:56.261299+00:00
-- url     : https://prove2.me/submissions/897eb996-2823-425e-9dd1-03fc3bf202bb

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_ja18l_intrinsic_residual_limit_zero_origin
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The original jump difference J has the zero initial value. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (R : ℝ≥0 → Ω → ℝ)
    (hRsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto
        (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (nhds (R t ω))) :
    ∀ᵐ ω ∂P,
      X.X 0 ω - ((0 : ℝ≥0) : ℝ) *
        (∫ η, X.X 1 η ∂P) - R 0 ω = 0 := by
  have hR0 := avram_ja18l_intrinsic_residual_limit_zero_origin
    X R hRsource
  filter_upwards [hR0] with ω hω
  simp [X.X_zero ω, hω]
