-- Prove2me | solution 1 for AvramDividend.Classical.chat04_shifted_scale_past_event_condExp
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T06:33:47.176622+00:00
-- url     : https://prove2.me/submissions/bb46713a-b390-475b-9360-399b42a66014

import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.IdentDistrib
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.Probability.Process.Adapted
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_scale_function_borel_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

/-!
The scale payoff's conditional Markov expectation is preserved when
restricted to any event known at the past time s. Essential for the killed
process, where the historical survival event is past-measurable.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (s t : ℝ≥0) (hst : s ≤ t) (x : ℝ)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A)
    (hInt : Integrable (fun ω => W (x + X.X (t - s) ω)) P) :
    P[A.indicator (fun ω => W (x + (X.X t ω - X.X s ω))) | 𝓕 s] =ᵐ[P]
      A.indicator (fun _ => ∫ ω, W (x + X.X (t - s) ω) ∂P) := by
  let F : Ω → ℝ := fun ω => W (x + (X.X t ω - X.X s ω))
  let g : Ω → ℝ := fun ω => X.X t ω - X.X s ω
  let f : ℝ → ℝ := fun y => W (x + y)
  letI : IsProbabilityMeasure P := X.isProbability
  have hWt : Measurable W :=
    AvramDividend.Classical.chat03_scale_function_borel_measurable X q W hW
  have hf : Measurable f := by
    dsimp [f]
    exact hWt.comp (measurable_const.add measurable_id)
  have hXt : Measurable (X.X t) :=
    (X.adapted t).mono (𝓕.le t) le_rfl
  have hXs : Measurable (X.X s) :=
    (X.adapted s).mono (𝓕.le s) le_rfl
  have hFm : Measurable F := by
    dsimp [F]
    exact hf.comp (hXt.sub hXs)
  have hFstrong :
      StronglyMeasurable[MeasurableSpace.comap F inferInstance] F :=
    (comap_measurable F).stronglyMeasurable
  have hle :
      (MeasurableSpace.comap f inferInstance).comap g ≤
        (inferInstance : MeasurableSpace ℝ).comap g :=
    MeasurableSpace.comap_mono hf.comap_le
  have hle' :
      MeasurableSpace.comap F inferInstance ≤
        MeasurableSpace.comap g inferInstance := by
    simpa only [MeasurableSpace.comap_comp, Function.comp_def,
      F, f, g] using hle
  have hi : Indep (MeasurableSpace.comap F inferInstance) (𝓕 s) P :=
    indep_of_indep_of_le_left (X.indepIncrements s t hst) hle'
  have hid : IdentDistrib F
      (fun ω => W (x + X.X (t - s) ω)) P P := by
    simpa only [Function.comp_def, F, f, g] using
      (X.stationaryIncrements s t hst).comp hf
  have hFI : Integrable F P := hid.integrable_iff.mpr hInt
  have hE :
      (∫ ω, F ω ∂P) =
        ∫ ω, W (x + X.X (t - s) ω) ∂P :=
    hid.integral_eq
  have hCE := condExp_indep_eq hFm.comap_le (𝓕.le s) hFstrong hi
  have hMarkov :
      P[F | 𝓕 s] =ᵐ[P]
        (fun _ => ∫ ω, W (x + X.X (t - s) ω) ∂P) := by
    simpa only [hE] using hCE
  have hIndicator :
      P[A.indicator F | 𝓕 s] =ᵐ[P]
        A.indicator (P[F | 𝓕 s]) :=
    condExp_indicator hFI hA
  change P[A.indicator F | 𝓕 s] =ᵐ[P]
    A.indicator (fun _ => ∫ ω, W (x + X.X (t - s) ω) ∂P)
  filter_upwards [hIndicator, hMarkov] with ω hI hM
  rw [hI]
  by_cases hw : ω ∈ A
  · simp [Set.indicator_of_mem hw, hM]
  · simp [Set.indicator, hw]
