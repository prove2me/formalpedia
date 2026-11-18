-- Prove2me | solution 1 for AvramDividend.Classical.avram_a27_original_physical_marked_joint_PGF_sharp_Poisson_sandwich_20261117
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T23:52:44.497453+00:00
-- url     : https://prove2.me/submissions/8ae10685-e253-4a5b-be22-3facbddb21f9

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a27_original_negative_mark_pgf_lower_bounded_by_physical_void_20261117
import Theorems.Thm_AvramDividend_Classical_avram_a27_original_marked_pgf_expected_le_physical_Poisson_count_pgf_20261117
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

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
      ∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
      else 0)
    (K : Ω → ℕ) (hK : Measurable K)
    (r : ℝ≥0) (hLaw : HasLaw K (poissonMeasure r) P)
    (hCount : ∀ᵐ ω ∂P, (K ω : ℝ) =
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 t ×ˢ Iio (0 : ℝ))).toReal)
    (z : ℝ) (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    Real.exp (-(r : ℝ)) ≤
      (∫ ω, z ^ (K ω) * Real.exp (θ * J ω) ∂P) ∧
    (∫ ω, z ^ (K ω) * Real.exp (θ * J ω) ∂P) ≤
      Real.exp ((r : ℝ) * (z - 1)) := by
  constructor
  · exact avram_a27_original_negative_mark_pgf_lower_bounded_by_physical_void_20261117
      X hFinite t θ hθ J hJMeas hJEq K hK r hLaw hCount z hz hz1
  · exact avram_a27_original_marked_pgf_expected_le_physical_Poisson_count_pgf_20261117
      X hFinite t θ hθ J hJMeas hJEq K hK r hLaw z hz hz1
