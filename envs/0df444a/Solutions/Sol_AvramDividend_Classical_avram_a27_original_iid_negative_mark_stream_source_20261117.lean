-- Prove2me | solution 1 for AvramDividend.Classical.avram_a27_original_iid_negative_mark_stream_source_20261117
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T15:57:39.383707+00:00
-- url     : https://prove2.me/submissions/31fbcd9f-887d-44d9-b820-045eb6531c61
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a99_original_measurable_physical_marked_jump_measure_dirac_enumeration_20261114
import Theorems.Thm_AvramDividend_Classical_avram_bridge20261123_A27_iid_marks_of_physical_dirac_enumeration
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
      ∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
        X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u
      else 0)
    (K : Ω → ℕ) (r : ℝ≥0)
    (hK : Measurable K) (hLaw : HasLaw K (poissonMeasure r) P)
    (hCount : ∀ᵐ ω ∂P, (K ω : ℝ) =
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 t ×ˢ Iio (0 : ℝ))).toReal)
    (hRate : (r : ℝ) =
      ((t : ℝ≥0∞) * X.ν (Iio (0 : ℝ))).toReal) :
    ∃ (Y : ℕ → Ω → ℝ) (m : ℝ),
      (∀ n, Measurable (Y n)) ∧
      IndepFun K (fun ω n => Y n ω) P ∧
      iIndepFun Y P ∧
      (∀ n : ℕ, IdentDistrib (Y n) (Y 0) P P) ∧
      (∀ᵐ ω ∂P, J ω = ∑ j ∈ Finset.range (K ω), Y j ω) ∧
      (∀ k : ℕ,
        (∫ ω, Real.exp (θ * ∑ j ∈ Finset.range k, Y j ω) ∂P) =
          m ^ k) ∧
      (r : ℝ) * (m - 1) =
        (t : ℝ) * (∫ y in Iio (0 : ℝ),
          Real.exp (θ * y) - 1 ∂X.ν) := by
  have hSource :=
    AvramDividend.Classical.avram_a99_original_measurable_physical_marked_jump_measure_dirac_enumeration_20261114 X
  exact
    AvramDividend.Classical.avram_bridge20261123_A27_iid_marks_of_physical_dirac_enumeration
      X hFinite hNu t ht θ hθ J hJMeas hJEq
      K r hK hLaw hCount hRate hSource
