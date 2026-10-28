-- Prove2me | solution 1 for FunctionalInequalities.KLS.BKL.Localization.IsEldanCutoff.continuous_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:04:41.641521+00:00
-- url     : https://prove2.me/submissions/804e7215-dcb9-4123-a267-9987e4cf65f9

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Diffusion_Transport
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_Process_Basic

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace
open FunctionalInequalities.Probability.Diffusion
section
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim LevyStochCalc.Brownian.Ito
section Transport
variable {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] {N d : ℕ}
  {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d} {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›}
  {hW : ∀ k, LevyStochCalc.Brownian.IsBrownianFiltration (W.W k) ℱ}
/-- Every path of a diffusion is continuous. -/
theorem FunctionalInequalities.Probability.Diffusion.IsDiffusion.continuous_path {b : (Fin N → ℝ) → Fin N → ℝ} {σ : (Fin N → ℝ) → Fin d → Fin N → ℝ}
    {x₀ : Fin N → ℝ} {Y : ℝ → Ω → Fin N → ℝ} (h : IsDiffusion W ℱ hW b σ x₀ Y) (ω : Ω) :
    Continuous fun t => Y t ω := by
  obtain ⟨_, _, _, hv⟩ := h
  exact hv.continuous_path ω
end Transport
end
end
end

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
  FunctionalInequalities.Probability.Diffusion
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim LevyStochCalc.Brownian.Ito
variable {n : ℕ} (μ : MeasureTheory.ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hc : IsCompact (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))).support)
section Process
variable {μ hc} {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
  {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P n} {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›}
  {hW : ∀ k, LevyStochCalc.Brownian.IsBrownianFiltration (W.W k) ℱ} {γ : FunctionalInequalities.KLS.BKL.Localization.Param n → ℝ} {p : ℝ → Ω → FunctionalInequalities.KLS.BKL.Localization.Param n}
/-- Paths of the cutoff Eldan process are continuous everywhere. -/
theorem solution (h : FunctionalInequalities.KLS.BKL.Localization.IsEldanCutoff μ hc W ℱ hW γ p) (ω : Ω) :
    Continuous fun t => p t ω := by
  let Φ : FunctionalInequalities.KLS.BKL.Localization.Param n ≃L[ℝ] (Fin (Module.finrank ℝ (FunctionalInequalities.KLS.BKL.Localization.Param n)) → ℝ) :=
    FunctionalInequalities.Probability.Diffusion.stateEquiv (FunctionalInequalities.KLS.BKL.Localization.Param n)
  change FunctionalInequalities.Probability.Diffusion.IsDiffusion W ℱ hW
    (FunctionalInequalities.Probability.Diffusion.transportDrift Φ (FunctionalInequalities.KLS.BKL.Localization.cutoffDrift μ hc γ))
    (FunctionalInequalities.Probability.Diffusion.transportNoise Φ (FunctionalInequalities.KLS.BKL.Localization.cutoffNoise μ hc γ)) (Φ 0)
    (fun t ω => Φ (p t ω)) at h
  have hp := FunctionalInequalities.Probability.Diffusion.IsDiffusion.continuous_path h ω
  have hp' := Φ.symm.continuous.comp hp
  have he :
      (Φ.symm ∘ (fun t => Φ (p t ω))) =
        (fun t => Φ.symm (Φ (p t ω))) := by
    funext t
    rfl
  rw [he] at hp'
  simpa only [ContinuousLinearEquiv.symm_apply_apply] using hp'
