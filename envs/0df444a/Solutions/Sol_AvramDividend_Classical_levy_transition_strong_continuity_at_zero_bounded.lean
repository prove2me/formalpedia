-- Prove2me | solution 1 for AvramDividend.Classical.levy_transition_strong_continuity_at_zero_bounded
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T22:00:42.310279+00:00
-- url     : https://prove2.me/submissions/85856257-db0f-4bc3-9c12-ac31468f0d47

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Probability.Process.Adapted
import Mathlib.Topology.Instances.NNReal.Lemmas
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (f : ℝ → ℝ) (hf : Continuous f)
    (B : ℝ) (hB : ∀ y : ℝ, ‖f y‖ ≤ B)
    (x : ℝ) (τ : ℕ → ℝ≥0)
    (hτ : Filter.Tendsto τ Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun n => ∫ ω, f (x + X.X (τ n) ω) ∂P)
      Filter.atTop (nhds (f x)) := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hmeas (n : ℕ) :
      AEStronglyMeasurable (fun ω => f (x + X.X (τ n) ω)) P := by
    have hXm : Measurable (X.X (τ n)) :=
      (X.adapted (τ n)).mono (𝓕.le (τ n)) le_rfl
    exact (hf.measurable.comp (measurable_const.add hXm)).aestronglyMeasurable
  have hlim (ω : Ω) :
      Filter.Tendsto (fun n => f (x + X.X (τ n) ω))
        Filter.atTop (nhds (f x)) := by
    have hτwithin :
        Filter.Tendsto τ Filter.atTop (𝓝[Ici (0 : ℝ≥0)] 0) := by
      apply tendsto_nhdsWithin_iff.mpr
      exact ⟨hτ, Filter.Eventually.of_forall
        (fun n => Set.mem_Ici.mpr (show (0 : ℝ≥0) ≤ τ n from bot_le))⟩
    have hXlim : Filter.Tendsto (fun n => X.X (τ n) ω)
        Filter.atTop (nhds 0) := by
      simpa only [Function.comp_def, X.X_zero ω] using
        ((X.rightCont ω 0).tendsto.comp hτwithin)
    have hAdd : Filter.Tendsto (fun n => x + X.X (τ n) ω)
        Filter.atTop (nhds (x + 0)) :=
      tendsto_const_nhds.add hXlim
    simpa only [Function.comp_def, add_zero] using
      (hf.continuousAt.tendsto.comp hAdd)
  have hmain :
      Filter.Tendsto
        (fun n => ∫ ω, f (x + X.X (τ n) ω) ∂P)
        Filter.atTop
        (nhds (∫ ω, f x ∂P)) := by
    apply MeasureTheory.tendsto_integral_of_dominated_convergence
      (fun _ : Ω => B)
    · exact hmeas
    · exact integrable_const B
    · intro n
      filter_upwards [] with ω
      exact hB (x + X.X (τ n) ω)
    · filter_upwards [] with ω
      exact hlim ω
  simpa using hmain
