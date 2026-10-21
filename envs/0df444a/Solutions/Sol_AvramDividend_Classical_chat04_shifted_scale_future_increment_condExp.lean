-- Prove2me | solution 1 for AvramDividend.Classical.chat04_shifted_scale_future_increment_condExp
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T06:26:59.851406+00:00
-- url     : https://prove2.me/submissions/07cc45e4-aad1-4427-ab88-4a107951388a

import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.IdentDistrib
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
Deterministic-capital Markov conditional expectation for the q-scale payoff.
The future increment is independent of the past and stationary; W is fully
Borel measurable, including its possible bounded-variation jump at zero.
The actual killed-scale martingale remains a separate result.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (s t : ℝ≥0) (hst : s ≤ t) (x : ℝ)
    (hInt : Integrable (fun ω => W (x + X.X (t - s) ω)) P) :
    P[(fun ω => W (x + (X.X t ω - X.X s ω))) | 𝓕 s] =ᵐ[P]
      (fun _ => ∫ ω, W (x + X.X (t - s) ω) ∂P) := by
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
  change P[F | 𝓕 s] =ᵐ[P]
    (fun _ => ∫ ω, W (x + X.X (t - s) ω) ∂P)
  simpa only [hE] using hCE
