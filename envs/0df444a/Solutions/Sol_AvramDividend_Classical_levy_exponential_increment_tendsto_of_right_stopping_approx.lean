-- Prove2me | solution 1 for AvramDividend.Classical.levy_exponential_increment_tendsto_of_right_stopping_approx
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T09:25:20.624775+00:00
-- url     : https://prove2.me/submissions/0df97485-f194-467f-a255-43fac7006202

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0) (τn : ℕ → Ω → ℝ≥0)
    (habove : ∀ ω n, τ ω ≤ τn n ω)
    (hconv : ∀ ω, Tendsto (fun n => τn n ω) atTop (𝓝 (τ ω)))
    (h : ℝ≥0) (θ : ℝ) (ω : Ω) :
    Tendsto
      (fun n => Real.exp (θ *
        (X.X (τn n ω + h) ω - X.X (τn n ω) ω)))
      atTop
      (𝓝 (Real.exp (θ *
        (X.X (τ ω + h) ω - X.X (τ ω) ω)))) := by
  have hright : Tendsto (fun n => τn n ω) atTop
      (𝓝[Set.Ici (τ ω)] (τ ω)) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨hconv ω, Filter.Eventually.of_forall
        (fun n => Set.mem_Ici.mpr (habove ω n))⟩
  have hcStart : Tendsto (fun r : ℝ≥0 => X.X r ω)
      (𝓝[Set.Ici (τ ω)] (τ ω)) (𝓝 (X.X (τ ω) ω)) :=
    X.rightCont ω (τ ω)
  have hXstart : Tendsto (fun n => X.X (τn n ω) ω) atTop
      (𝓝 (X.X (τ ω) ω)) :=
    hcStart.comp hright
  have hconvPlus : Tendsto (fun n => τn n ω + h) atTop
      (𝓝 (τ ω + h)) :=
    (hconv ω).add tendsto_const_nhds
  have hrightPlus : Tendsto (fun n => τn n ω + h) atTop
      (𝓝[Set.Ici (τ ω + h)] (τ ω + h)) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨hconvPlus, Filter.Eventually.of_forall
        (fun n => Set.mem_Ici.mpr (by
          simpa [add_comm] using (add_le_add_right (habove ω n) h)))⟩
  have hcEnd : Tendsto (fun r : ℝ≥0 => X.X r ω)
      (𝓝[Set.Ici (τ ω + h)] (τ ω + h))
      (𝓝 (X.X (τ ω + h) ω)) :=
    X.rightCont ω (τ ω + h)
  have hXend : Tendsto (fun n => X.X (τn n ω + h) ω) atTop
      (𝓝 (X.X (τ ω + h) ω)) :=
    hcEnd.comp hrightPlus
  have hdelta := hXend.sub hXstart
  have hscaled := (tendsto_const_nhds (x := θ)).mul hdelta
  exact Real.continuous_exp.continuousAt.tendsto.comp hscaled
