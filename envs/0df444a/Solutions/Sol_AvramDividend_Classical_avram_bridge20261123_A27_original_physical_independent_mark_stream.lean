-- Prove2me | solution 1 for AvramDividend.Classical.avram_bridge20261123_A27_original_physical_independent_mark_stream
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T14:16:57.351796+00:00
-- url     : https://prove2.me/submissions/eff0ed74-0e9d-4021-b618-89d5793d2aa0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a104_original_given_poisson_count_independent_physical_negative_mark_stream_20261114
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
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
      (∀ i, Measurable (Y i)) ∧
      (∀ k, IndepFun K
        (fun ω => ∑ i ∈ Finset.range k, Y i ω) P) ∧
      (∀ᵐ ω ∂P, J ω = ∑ i ∈ Finset.range (K ω), Y i ω) ∧
      (∀ k, (∫ ω, Real.exp
        (θ * ∑ i ∈ Finset.range k, Y i ω) ∂P) = m ^ k) ∧
      (r : ℝ) * (m - 1) =
        (t : ℝ) * (∫ y in Iio (0 : ℝ),
          Real.exp (θ * y) - 1 ∂X.ν) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  obtain ⟨Y, m, hY, hIndep, hRep, hFixed, hRate⟩ :=
    AvramDividend.Classical.avram_a104_original_given_poisson_count_independent_physical_negative_mark_stream_20261114
      X hFinite hNu t ht θ hθ J hJMeas hJEq K r hK hLaw hCount hRate
  refine ⟨Y, m, hY, ?_, hRep, hFixed, hRate⟩
  intro k
  have hSumMeas : Measurable
      (fun v : ℕ → ℝ => ∑ i ∈ Finset.range k, v i) := by
    apply Finset.measurable_sum
    intro i hi
    exact measurable_pi_apply i
  have h := ProbabilityTheory.IndepFun.comp hIndep
    measurable_id hSumMeas
  simpa only [Function.comp_def, id_eq] using h
