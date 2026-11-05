-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_b_smalljump_original_disjoint_mark_conditional_cross_zero_of_independence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T07:46:52.368055+00:00
-- url     : https://prove2.me/submissions/8d500c5c-6d19-445e-b3c2-0faafd85fa25

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_independent_disjoint_mark_band_orthogonality

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical ProbabilityTheory
open scoped NNReal ENNReal

/-- Physical conditional cross-orthogonality for two disjoint genuine
intrinsic mark cells, with source count independence and future-past independence. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (A B : Set ℝ) (hDisjoint : Disjoint A B)
    (JA JB : Ω → ℝ)
    (hSourceA : ∀ ω, JA ω =
      (((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ A)).toReal)
    (hSourceB : ∀ ω, JB ω =
      (((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)).toReal)
    (hJA : Integrable JA P) (hJB : Integrable JB P)
    (hProductInt : Integrable (fun ω => JA ω * JB ω) P)
    (hMeasA : AEStronglyMeasurable JA P)
    (hMeasB : AEStronglyMeasurable JB P)
    (hIndependentAB : IndepFun JA JB P)
    (rA rB : ℝ)
    (hRateA : rA = ((((t - s : ℝ≥0) : ℝ≥0∞) * X.ν A)).toReal)
    (hRateB : rB = ((((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B)).toReal)
    (hFirstA : (∫ ω, JA ω ∂P) = rA)
    (hFirstB : (∫ ω, JB ω ∂P) = rB)
    (mFuture : MeasurableSpace Ω) (hFuture : mFuture ≤ mΩ)
    (hCrossStrong : StronglyMeasurable[mFuture] (fun ω =>
      (JA ω - rA) * (JB ω - rB)))
    (hFutureIndependent : Indep mFuture (𝓕 s) P) :
    P[(fun ω => (JA ω - rA) * (JB ω - rB)) | 𝓕 s] =ᵐ[P]
      (fun _ => (0 : ℝ)) := by
  letI : MeasurableSpace Ω := mΩ
  have hCross :
      (∫ ω, (JA ω - rA) * (JB ω - rB) ∂P) = 0 :=
    avram_p4_b_smalljump_original_independent_disjoint_mark_band_orthogonality
      X s t A B hDisjoint JA JB hSourceA hSourceB hJA hJB
      hProductInt hMeasA hMeasB hIndependentAB rA rB
      hRateA hRateB hFirstA hFirstB
  have hIndep := condExp_indep_eq hFuture (𝓕.le s)
    hCrossStrong hFutureIndependent
  simpa only [hCross] using hIndep
