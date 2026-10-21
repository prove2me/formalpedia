-- Prove2me | solution 1 for AvramDividend.Classical.chat04_general_future_increment_conditional_expectation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T22:50:00.07409+00:00
-- url     : https://prove2.me/submissions/73d0a24d-f59b-4ccc-95de-7b4a6e4b3884

import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Process.Adapted
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

/-!
The conditional law of a Lévy increment applies to every Borel integrable
payoff φ, not only the q-scale W. This deterministic-start Markov kernel
identity follows from full-filtration independent and stationary increments.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (φ : ℝ → ℝ) (hφ : Measurable φ)
    (hInt : Integrable (fun ω => φ (X.X (t - s) ω)) P) :
    P[(fun ω => φ (X.X t ω - X.X s ω)) | 𝓕 s] =ᵐ[P]
      (fun _ => ∫ ω, φ (X.X (t - s) ω) ∂P) := by
  let F : Ω → ℝ := fun ω => φ (X.X t ω - X.X s ω)
  let g : Ω → ℝ := fun ω => X.X t ω - X.X s ω
  letI : IsProbabilityMeasure P := X.isProbability
  have hXt : Measurable (X.X t) :=
    (X.adapted t).mono (𝓕.le t) le_rfl
  have hXs : Measurable (X.X s) :=
    (X.adapted s).mono (𝓕.le s) le_rfl
  have hFm : Measurable F := by
    dsimp [F]
    exact hφ.comp (hXt.sub hXs)
  have hFstrong :
      StronglyMeasurable[MeasurableSpace.comap F inferInstance] F :=
    (comap_measurable F).stronglyMeasurable
  have hle :
      (MeasurableSpace.comap φ inferInstance).comap g ≤
        (inferInstance : MeasurableSpace ℝ).comap g :=
    MeasurableSpace.comap_mono hφ.comap_le
  have hle' :
      MeasurableSpace.comap F inferInstance ≤
        MeasurableSpace.comap g inferInstance := by
    simpa only [MeasurableSpace.comap_comp, Function.comp_def,
      F, g] using hle
  have hi : Indep (MeasurableSpace.comap F inferInstance) (𝓕 s) P :=
    indep_of_indep_of_le_left (X.indepIncrements s t hst) hle'
  have hid : IdentDistrib F
      (fun ω => φ (X.X (t - s) ω)) P P := by
    simpa only [Function.comp_def, F, g] using
      (X.stationaryIncrements s t hst).comp hφ
  have hFI : Integrable F P := hid.integrable_iff.mpr hInt
  have hE :
      (∫ ω, F ω ∂P) =
        ∫ ω, φ (X.X (t - s) ω) ∂P :=
    hid.integral_eq
  have hCE := condExp_indep_eq hFm.comap_le (𝓕.le s) hFstrong hi
  change P[F | 𝓕 s] =ᵐ[P]
    (fun _ => ∫ ω, φ (X.X (t - s) ω) ∂P)
  simpa only [hE] using hCE
