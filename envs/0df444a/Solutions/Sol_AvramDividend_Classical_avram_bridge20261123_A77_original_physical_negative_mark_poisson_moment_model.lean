-- Prove2me | solution 1 for AvramDividend.Classical.avram_bridge20261123_A77_original_physical_negative_mark_poisson_moment_model
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T15:33:20.843313+00:00
-- url     : https://prove2.me/submissions/d3d64680-083a-42d1-82b4-99475f466d4d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bridge20261123_A77_positive_original_marked_poisson_moment_from_A92
import Theorems.Thm_AvramDividend_Classical_avram_bridge20261123_A77_degenerate_original_physical_poisson_moment
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
    ∃ (N : Ω → ℕ) (r : ℝ≥0) (m : ℝ),
      HasLaw N (poissonMeasure r) P ∧
      (∫ ω, Real.exp (θ * J ω) ∂P) =
        ∫ ω, m ^ (N ω) ∂P ∧
      (r : ℝ) * (m - 1) =
        (t : ℝ) *
          (∫ y in Iio (0 : ℝ), Real.exp (θ * y) - 1 ∂X.ν) := by
  by_cases hνzero : X.ν = 0
  · exact
      AvramDividend.Classical.avram_bridge20261123_A77_degenerate_original_physical_poisson_moment
        X hFinite t θ hθ J hJMeas hJEq (Or.inl hνzero)
  by_cases htzero : t = 0
  · exact
      AvramDividend.Classical.avram_bridge20261123_A77_degenerate_original_physical_poisson_moment
        X hFinite t θ hθ J hJMeas hJEq (Or.inr (Or.inl htzero))
  by_cases hθzero : θ = 0
  · exact
      AvramDividend.Classical.avram_bridge20261123_A77_degenerate_original_physical_poisson_moment
        X hFinite t θ hθ J hJMeas hJEq (Or.inr (Or.inr hθzero))
  have htpos : 0 < t := lt_of_le_of_ne (zero_le : (0 : ℝ≥0) ≤ t) (Ne.symm htzero)
  have hθpos : 0 < θ := lt_of_le_of_ne hθ (Ne.symm hθzero)
  exact
    AvramDividend.Classical.avram_bridge20261123_A77_positive_original_marked_poisson_moment_from_A92
      X hFinite t θ hθ J hJMeas hJEq hνzero htpos hθpos
