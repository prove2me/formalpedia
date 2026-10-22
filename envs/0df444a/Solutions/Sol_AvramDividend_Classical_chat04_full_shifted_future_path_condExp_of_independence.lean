-- Prove2me | solution 1 for AvramDividend.Classical.chat04_full_shifted_future_path_condExp_of_independence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T06:57:10.696513+00:00
-- url     : https://prove2.me/submissions/e8830858-f945-45d1-b2f5-00c956ca57c5

import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Independence.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

/-!
Conditional Markov expectation for EVERY integrable Borel functional of
the full uncountable-time shifted future Lévy path, GIVEN its independence
from the entire past filtration. This is a generic analytic interface,
and does not pretend to derive full-path independence or q-harmonicity.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0)
    (hFuture : Indep
      (MeasurableSpace.comap
        (fun ω : Ω => fun t : ℝ≥0 => X.X (s + t) ω - X.X s ω)
        inferInstance)
      (𝓕 s) P)
    (f : (ℝ≥0 → ℝ) → ℝ) (hf : Measurable f)
    (hInt : Integrable
      (fun ω => f (fun t => X.X (s + t) ω - X.X s ω)) P) :
    P[(fun ω => f (fun t => X.X (s + t) ω - X.X s ω)) | 𝓕 s] =ᵐ[P]
      (fun _ => ∫ ω, f (fun t => X.X (s + t) ω - X.X s ω) ∂P) := by
  letI : IsProbabilityMeasure P := X.isProbability
  let Y : Ω → (ℝ≥0 → ℝ) :=
    fun ω t => X.X (s + t) ω - X.X s ω
  let F : Ω → ℝ := fun ω => f (Y ω)
  have hY : Measurable Y := by
    apply measurable_pi_iff.mpr
    intro t
    have ht : Measurable (X.X (s + t)) :=
      (X.adapted (s + t)).mono (𝓕.le (s + t)) le_rfl
    have hs : Measurable (X.X s) :=
      (X.adapted s).mono (𝓕.le s) le_rfl
    exact ht.sub hs
  have hFm : Measurable F := hf.comp hY
  have hStrong :
      StronglyMeasurable[MeasurableSpace.comap F inferInstance] F :=
    (comap_measurable F).stronglyMeasurable
  have hle :
      MeasurableSpace.comap F inferInstance ≤
        MeasurableSpace.comap Y inferInstance := by
    have h0 :
        (MeasurableSpace.comap f inferInstance).comap Y ≤
          (inferInstance : MeasurableSpace (ℝ≥0 → ℝ)).comap Y :=
      MeasurableSpace.comap_mono hf.comap_le
    simpa only [MeasurableSpace.comap_comp, Function.comp_def,
      F] using h0
  have hFuture' :
      Indep (MeasurableSpace.comap Y inferInstance) (𝓕 s) P := by
    simpa only [Y] using hFuture
  have hi : Indep (MeasurableSpace.comap F inferInstance) (𝓕 s) P :=
    indep_of_indep_of_le_left hFuture' hle
  have hCE := condExp_indep_eq hFm.comap_le (𝓕.le s) hStrong hi
  change P[F | 𝓕 s] =ᵐ[P] (fun _ => ∫ ω, F ω ∂P)
  exact hCE
