-- Prove2me | solution 4 for AvramDividend.Classical.avram_a77_original_finite_activity_physical_negative_jump_compound_poisson_laplace_20261114
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T13:50:15.76362+00:00
-- url     : https://prove2.me/submissions/c029b696-25e0-47dd-8bbf-787e2dc2a923
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bridge20261123_A77_original_physical_negative_mark_poisson_moment_model
import Theorems.Thm_AvramDividend_Classical_avram_bridge20261123_A77_original_laplace_given_physical_poisson_moment
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (t : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ)
    (J : Ω → ℝ) (hJMeas : Measurable J)
    (hJEq : J =ᵐ[P] fun ω =>
      ∑' u : ℝ≥0,
        if 0 < u ∧ u ≤ t then
          X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u
        else 0) :
    (∫ ω, Real.exp (θ * J ω) ∂P) =
      Real.exp ((t : ℝ) *
        (∫ y in Iio (0 : ℝ), Real.exp (θ * y) - 1 ∂X.ν)) := by
  have hModel :=
    AvramDividend.Classical.avram_bridge20261123_A77_original_physical_negative_mark_poisson_moment_model
      X hFinite t θ hθ J hJMeas hJEq
  exact AvramDividend.Classical.avram_bridge20261123_A77_original_laplace_given_physical_poisson_moment
      X hFinite t θ hθ J hJMeas hJEq hModel
