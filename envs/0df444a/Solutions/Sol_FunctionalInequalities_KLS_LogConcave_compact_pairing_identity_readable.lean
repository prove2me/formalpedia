-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.compact_pairing_identity_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:38:00.563922+00:00
-- url     : https://prove2.me/submissions/9b0fd722-972e-4b96-94de-d99d235a7e66

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_BrascampLieb

noncomputable section
open MeasureTheory Filter Topology Set InnerProductSpace
open FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.KLS.LogConcave
open FunctionalInequalities.KLS.LogConcave.HeatSemigroup
open scoped ContDiff RealInnerProductSpace
section FiniteDimensional
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
/-- Compactness of the diffusion test gives integrability of both pairings,
even though the `C¹` function paired against it need not have compact support. -/
theorem solution
    {ν : ProbabilityMeasure E} (m : Measure E) [m.IsAddHaarMeasure]
    {U f u : E → ℝ} (hνU : (ν : Measure E) = m.tilted (-U))
    (hU : ContDiff ℝ 1 U) (hf : ContDiff ℝ 1 f)
    (hu : ContDiff ℝ ∞ u) (huc : HasCompactSupport u) :
    Integrable (fun x => f x * (-FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian U u x)) (ν : Measure E) ∧
      Integrable (fun x => ⟪gradient f x, gradient u x⟫) (ν : Measure E) ∧
      (∫ x, f x * (-FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian U u x) ∂(ν : Measure E)) =
        ∫ x, ⟪gradient f x, gradient u x⟫ ∂(ν : Measure E) := by
  have hu1 : ContDiff ℝ 1 u := hu.of_le (WithTop.coe_le_coe.mpr le_top)
  have hu2 : ContDiff ℝ 2 u := hu.of_le (WithTop.coe_le_coe.mpr le_top)
  have hLs : HasCompactSupport (fun x => -FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian U u x) := by
    simpa only [Function.comp_def] using
      ((FunctionalInequalities.Analysis.BakryEmery.hasCompactSupport_weightedLaplacian U huc).comp_left
        (g := fun t : ℝ => -t) (by simp))
  have hGs : HasCompactSupport (fun x => ⟪gradient f x, gradient u x⟫) := by
    refine HasCompactSupport.of_support_subset_isCompact
      (FunctionalInequalities.Analysis.BakryEmery.hasCompactSupport_gradient huc) fun x hx => subset_tsupport _ ?_
    rw [Function.mem_support] at hx ⊢
    intro hz
    exact hx (by rw [hz, inner_zero_right])
  have hpairInt :
      Integrable (fun x => f x * (-FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian U u x)) (ν : Measure E) :=
    (hf.continuous.mul (FunctionalInequalities.Analysis.BakryEmery.continuous_weightedLaplacian hU hu2).neg).integrable_of_hasCompactSupport
      hLs.mul_left
  have hgradInt :
      Integrable (fun x => ⟪gradient f x, gradient u x⟫) (ν : Measure E) :=
    ((FunctionalInequalities.Analysis.BakryEmery.continuous_gradient hf).inner (FunctionalInequalities.Analysis.BakryEmery.continuous_gradient hu1)).integrable_of_hasCompactSupport
      hGs
  refine ⟨hpairInt, hgradInt, ?_⟩
  have hibp := FunctionalInequalities.Analysis.BakryEmery.integral_inner_gradient_tilted m hU hu2 huc hf
  rw [← hνU] at hibp
  calc
    (∫ x, f x * (-FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian U u x) ∂(ν : Measure E)) =
        ∫ x, -FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian U u x * f x ∂(ν : Measure E) :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)
    _ = ∫ x, ⟪gradient u x, gradient f x⟫ ∂(ν : Measure E) := hibp.symm
    _ = ∫ x, ⟪gradient f x, gradient u x⟫ ∂(ν : Measure E) :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => real_inner_comm _ _)
