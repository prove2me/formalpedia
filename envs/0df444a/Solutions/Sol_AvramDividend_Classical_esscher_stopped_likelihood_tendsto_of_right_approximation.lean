-- Prove2me | solution 1 for AvramDividend.Classical.esscher_stopped_likelihood_tendsto_of_right_approximation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T14:07:46.365164+00:00
-- url     : https://prove2.me/submissions/6947318d-207f-4ae8-bf4a-c1a5bb229f38

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Topology
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (θ : ℝ) (hθ : 0 ≤ θ)
    (τ : Ω → ℝ≥0) (τn : ℕ → Ω → ℝ≥0)
    (hlim : ∀ ω, Tendsto (fun n => τn n ω) atTop (𝓝 (τ ω)))
    (habove : ∀ ω n, τ ω ≤ τn n ω) :
    ∀ ω, Tendsto
      (fun n => Real.exp (θ * X.X (τn n ω) ω -
        (τn n ω : ℝ) * X.ψ θ))
      atTop (𝓝 (Real.exp (θ * X.X (τ ω) ω -
        (τ ω : ℝ) * X.ψ θ))) := by
  intro ω
  have hright : Tendsto (fun n => τn n ω) atTop
      (𝓝[Set.Ici (τ ω)] (τ ω)) :=
    tendsto_nhdsWithin_iff.2
      ⟨hlim ω, Eventually.of_forall (fun n => habove ω n)⟩
  have hX : Tendsto (fun n => X.X (τn n ω) ω)
      atTop (𝓝 (X.X (τ ω) ω)) :=
    (X.rightCont ω _).tendsto.comp hright
  have ht : Tendsto (fun n => (τn n ω : ℝ))
      atTop (𝓝 (τ ω : ℝ)) :=
    (NNReal.continuous_coe.tendsto (τ ω)).comp (hlim ω)
  have hθX : Tendsto
      (fun n => θ * X.X (τn n ω) ω) atTop
      (𝓝 (θ * X.X (τ ω) ω)) :=
    tendsto_const_nhds.mul hX
  have htψ : Tendsto
      (fun n => (τn n ω : ℝ) * X.ψ θ) atTop
      (𝓝 ((τ ω : ℝ) * X.ψ θ)) :=
    ht.mul tendsto_const_nhds
  have hexp : Tendsto
      (fun n => θ * X.X (τn n ω) ω -
        (τn n ω : ℝ) * X.ψ θ) atTop
      (𝓝 (θ * X.X (τ ω) ω -
        (τ ω : ℝ) * X.ψ θ)) :=
    hθX.sub htψ
  exact (Real.continuous_exp.tendsto _).comp hexp
