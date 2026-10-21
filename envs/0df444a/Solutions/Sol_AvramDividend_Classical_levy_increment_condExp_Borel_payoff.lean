-- Prove2me | solution 1 for AvramDividend.Classical.levy_increment_condExp_Borel_payoff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T15:02:10.860349+00:00
-- url     : https://prove2.me/submissions/db6421b5-0083-47c0-9143-2a8899484a25

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

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (x : ℝ) (f : ℝ → ℝ) (hf : Measurable f)
    (hInt : Integrable (fun ω => f (x + X.X (t - s) ω)) P) :
    P[(fun ω => f (x + (X.X t ω - X.X s ω))) | 𝓕 s] =ᵐ[P]
      (fun _ => ∫ ω, f (x + X.X (t - s) ω) ∂P) := by
  let F : Ω → ℝ := fun ω => f (x + (X.X t ω - X.X s ω))
  let g : Ω → ℝ := fun ω => X.X t ω - X.X s ω
  let h : ℝ → ℝ := fun y => f (x + y)
  letI : IsProbabilityMeasure P := X.isProbability
  have hh : Measurable h := by
    dsimp [h]
    exact hf.comp (measurable_const.add measurable_id)
  have hXt : Measurable (X.X t) :=
    (X.adapted t).mono (𝓕.le t) le_rfl
  have hXs : Measurable (X.X s) :=
    (X.adapted s).mono (𝓕.le s) le_rfl
  have hFm : Measurable F := by
    dsimp [F]
    exact hh.comp (hXt.sub hXs)
  have hFstrong :
      StronglyMeasurable[MeasurableSpace.comap F inferInstance] F :=
    (comap_measurable F).stronglyMeasurable
  have hle :
      (MeasurableSpace.comap h inferInstance).comap g ≤
        (inferInstance : MeasurableSpace ℝ).comap g :=
    MeasurableSpace.comap_mono hh.comap_le
  have hle' :
      MeasurableSpace.comap F inferInstance ≤
        MeasurableSpace.comap g inferInstance := by
    simpa only [MeasurableSpace.comap_comp, Function.comp_def,
      F, h, g] using hle
  have hi : Indep (MeasurableSpace.comap F inferInstance) (𝓕 s) P :=
    indep_of_indep_of_le_left (X.indepIncrements s t hst) hle'
  have hid : IdentDistrib F
      (fun ω => f (x + X.X (t - s) ω)) P P := by
    simpa only [Function.comp_def, F, h, g] using
      (X.stationaryIncrements s t hst).comp hh
  have hFI : Integrable F P := hid.integrable_iff.mpr hInt
  have hE :
      (∫ ω, F ω ∂P) =
        ∫ ω, f (x + X.X (t - s) ω) ∂P :=
    hid.integral_eq
  have hCE := condExp_indep_eq hFm.comap_le (𝓕.le s) hFstrong hi
  change P[F | 𝓕 s] =ᵐ[P]
    (fun _ => ∫ ω, f (x + X.X (t - s) ω) ∂P)
  simpa only [hE] using hCE
