-- Prove2me | solution 1 for AvramDividend.Classical.levy_transition_right_time_continuity_bounded
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T22:14:27.524032+00:00
-- url     : https://prove2.me/submissions/e75c362a-ab24-4bc6-9442-519e4e3e2f7a

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
    (x : ℝ) (t : ℝ≥0) (τ : ℕ → ℝ≥0)
    (hτle : ∀ n, t ≤ τ n)
    (hτ : Filter.Tendsto τ Filter.atTop (nhds t)) :
    Filter.Tendsto
      (fun n => ∫ ω, f (x + X.X (τ n) ω) ∂P)
      Filter.atTop (nhds (∫ ω, f (x + X.X t ω) ∂P)) := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hmeas (n : ℕ) :
      AEStronglyMeasurable (fun ω => f (x + X.X (τ n) ω)) P := by
    have hXm : Measurable (X.X (τ n)) :=
      (X.adapted (τ n)).mono (𝓕.le (τ n)) le_rfl
    exact (hf.measurable.comp (measurable_const.add hXm)).aestronglyMeasurable
  have hτwithin : Filter.Tendsto τ Filter.atTop (𝓝[Ici t] t) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨hτ, Filter.Eventually.of_forall
      (fun n => Set.mem_Ici.mpr (hτle n))⟩
  have hlim (ω : Ω) :
      Filter.Tendsto (fun n => f (x + X.X (τ n) ω))
        Filter.atTop (nhds (f (x + X.X t ω))) := by
    have hXlim : Filter.Tendsto (fun n => X.X (τ n) ω)
        Filter.atTop (nhds (X.X t ω)) :=
      (X.rightCont ω t).tendsto.comp hτwithin
    have hAdd : Filter.Tendsto (fun n => x + X.X (τ n) ω)
        Filter.atTop (nhds (x + X.X t ω)) :=
      tendsto_const_nhds.add hXlim
    exact hf.continuousAt.tendsto.comp hAdd
  apply MeasureTheory.tendsto_integral_of_dominated_convergence
    (fun _ : Ω => B)
  · exact hmeas
  · exact integrable_const B
  · intro n
    filter_upwards [] with ω
    exact hB (x + X.X (τ n) ω)
  · filter_upwards [] with ω
    exact hlim ω
