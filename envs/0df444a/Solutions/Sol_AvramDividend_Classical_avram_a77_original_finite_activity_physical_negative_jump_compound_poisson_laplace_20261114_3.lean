-- Prove2me | solution 3 for AvramDividend.Classical.avram_a77_original_finite_activity_physical_negative_jump_compound_poisson_laplace_20261114
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T21:18:50.975808+00:00
-- url     : https://prove2.me/submissions/aa66275b-9197-4f9a-868c-443e93f0952c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

/- Original physical finite-activity marked negative jump Laplace.
   Sound reduction uses exactly the Proved original Poisson Borel count law,
   an Open finite-family SPATIAL joint independence source obligation,
   and an Open Poisson random-measure Laplace functional theorem.
   Time-grid independence or marginal Poisson laws cannot substitute for
   spatial finite-family independence. -/
import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a77_original_negative_Borel_spatial_counts_jointly_independent
import Theorems.Thm_AvramDividend_Classical_avram_a77_laplace_from_joint_negative_Borel_Poisson_counts
import Theorems.Thm_AvramDividend_Classical_avram_a20_original_negative_borel_count_poisson_law
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
  exact avram_a77_laplace_from_joint_negative_Borel_Poisson_counts
    X hFinite t θ hθ J hJMeas hJEq
    (fun n B hMeas hNeg hPair =>
      avram_a77_original_negative_Borel_spatial_counts_jointly_independent
        X hFinite t n B hMeas hNeg hPair)
    (fun B hB hNeg =>
      avram_a20_original_negative_borel_count_poisson_law
        X hFinite t B hB hNeg)

