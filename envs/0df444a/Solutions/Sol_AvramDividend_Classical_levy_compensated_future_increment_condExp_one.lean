-- Prove2me | solution 1 for AvramDividend.Classical.levy_compensated_future_increment_condExp_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T22:29:16.252072+00:00
-- url     : https://prove2.me/submissions/9fc38830-7e49-4554-8e83-b550c4c6c18e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_compensated_future_increment_expectation_one
import Theorems.Thm_AvramDividend_Classical_levy_compensated_future_increment_indep

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t) (θ : ℝ) (hθ : 0 ≤ θ) :
    P[(fun ω => Real.exp
      (θ * (X.X t ω - X.X s ω) - ((t - s : ℝ≥0) : ℝ) * X.ψ θ)) | 𝓕 s]
      =ᵐ[P] (fun _ => (1 : ℝ)) := by
  let F : Ω → ℝ := fun ω =>
    Real.exp (θ * (X.X t ω - X.X s ω) -
      ((t - s : ℝ≥0) : ℝ) * X.ψ θ)
  letI : IsProbabilityMeasure P := X.isProbability
  have hXt : Measurable (X.X t) :=
    (X.adapted t).mono (𝓕.le t) le_rfl
  have hXs : Measurable (X.X s) :=
    (X.adapted s).mono (𝓕.le s) le_rfl
  have hFm : Measurable F := by
    dsimp [F]
    fun_prop
  have hFstrong :
      StronglyMeasurable[MeasurableSpace.comap F inferInstance] F :=
    (comap_measurable F).stronglyMeasurable
  have hIndep :
      Indep (MeasurableSpace.comap F inferInstance) (𝓕 s) P :=
    levy_compensated_future_increment_indep X s t hst θ
  have hE : (∫ ω, F ω ∂P) = 1 :=
    levy_compensated_future_increment_expectation_one X s t hst θ hθ
  have hCE := condExp_indep_eq hFm.comap_le (𝓕.le s) hFstrong hIndep
  change P[F | 𝓕 s] =ᵐ[P] (fun _ => (1 : ℝ))
  simpa only [hE] using hCE
