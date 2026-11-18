-- Prove2me | solution 2 for AvramDividend.Classical.avram_a92_original_finite_negative_activity_marked_poisson_enumeration_20261114
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T16:14:25.073473+00:00
-- url     : https://prove2.me/submissions/f426e8a8-2f08-482d-a74b-ca6b1260b17b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a20_original_negative_borel_count_poisson_law
import Theorems.Thm_AvramDividend_Classical_avram_a27_original_iid_negative_mark_stream_source_20261117
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) (hNu : X.ν ≠ 0)
    (t : ℝ≥0) (ht : 0 < t) (θ : ℝ) (hθ : 0 < θ)
    (J : Ω → ℝ) (hJMeas : Measurable J)
    (hJEq : J =ᵐ[P] fun ω =>
      ∑' u : ℝ≥0,
        if 0 < u ∧ u ≤ t then
          X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u
        else 0) :
    ∃ (N : Ω → ℕ) (Y : ℕ → Ω → ℝ) (r : ℝ≥0) (m : ℝ),
      Measurable N ∧ (∀ n, Measurable (Y n)) ∧
      IndepFun N (fun ω n => Y n ω) P ∧
      HasLaw N (poissonMeasure r) P ∧
      (∀ᵐ ω ∂P, J ω = ∑ j ∈ Finset.range (N ω), Y j ω) ∧
      (∀ k : ℕ,
        (∫ ω, Real.exp (θ * ∑ j ∈ Finset.range k, Y j ω) ∂P) =
          m ^ k) ∧
      (r : ℝ) * (m - 1) =
        (t : ℝ) * (∫ y in Iio (0 : ℝ),
          Real.exp (θ * y) - 1 ∂X.ν) := by
  classical
  obtain ⟨K, r, hK, hLaw, hCount, hRate⟩ :=
    avram_a20_original_negative_borel_count_poisson_law
      X hFinite t (Iio (0 : ℝ)) measurableSet_Iio (Subset.rfl)
  obtain ⟨Y, m, hY, hKY, hIID, hSame, hJ, hMom, hRateM⟩ :=
    avram_a27_original_iid_negative_mark_stream_source_20261117
      X hFinite hNu t ht θ hθ J hJMeas hJEq
      K r hK hLaw hCount hRate
  exact ⟨K, Y, r, m, hK, hY, hKY, hLaw, hJ, hMom, hRateM⟩
