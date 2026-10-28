-- Prove2me | solution 1 for FunctionalInequalities.KLS.CEK.bounded_source_lipschitz_primal_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:22:14.940756+00:00
-- url     : https://prove2.me/submissions/25eb8a50-ba08-493f-ac15-97be3252680d

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_CEK_BoundedPrimal
import Theorems.Thm_FunctionalInequalities_Analysis_lipschitzWith_real_legendre_readable
import Theorems.Thm_FunctionalInequalities_Analysis_real_convexOn_legendre_readable
import Theorems.Thm_FunctionalInequalities_KLS_CEK_bounded_source_finite_conjugate_readable
import Theorems.Thm_FunctionalInequalities_Probability_MomentMeasure_real_legendre_normalization_readable

noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal Topology RealInnerProductSpace
open FunctionalInequalities
open FunctionalInequalities.Analysis
open FunctionalInequalities.KLS
open FunctionalInequalities.Probability
open FunctionalInequalities.Probability.MomentMeasure
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
/-- Weak source-law-linked normalized primal. Every new conclusion is derived
from `bounded_source_finite_conjugate` for this actual bounded isotropic source.
No convexity, Lipschitz, integrability, normalization, or optimizer premise is
added to the source interface. The original finite-conjugate data are retained. -/
theorem solution
    (μ : ProbabilityMeasure E) (hμ : FunctionalInequalities.KLS.Isotropic μ) (L : NNReal)
    (hL : ∀ᵐ y ∂(μ : Measure E), ‖y‖ ≤ (L : ℝ)) :
    ∃ (q : E → EReal) (a : E) (m : ℝ) (ψ : E → ℝ),
      FunctionalInequalities.Analysis.ConvexPotential q ∧
      LowerSemicontinuous q ∧
      FunctionalInequalities.Probability.MomentMeasure.PotentialIntegrable q (μ : Measure E) ∧
      (∀ y, q y ≠ ⊤ → y ∈ closedBall (0 : E) (L : ℝ)) ∧
      a ∈ closedBall (0 : E) (L : ℝ) ∧
      q a = (m : EReal) ∧
      (∀ y, (m : EReal) ≤ q y) ∧
      (∀ x, FunctionalInequalities.Analysis.legendre q x ≠ ⊤ ∧ FunctionalInequalities.Analysis.legendre q x ≠ ⊥) ∧
      (∀ x, FunctionalInequalities.Analysis.legendre q x ≤ (((L : ℝ) * ‖x‖ - m : ℝ) : EReal)) ∧
      ψ = (fun x => (FunctionalInequalities.Analysis.legendre q x).toReal) ∧
      (∀ x, FunctionalInequalities.Analysis.legendre q x = (ψ x : EReal)) ∧
      FunctionalInequalities.Probability.MomentMeasure.mass (volume : Measure E) (FunctionalInequalities.Analysis.legendre q) = 1 ∧
      ConvexOn ℝ (univ : Set E) ψ ∧
      LipschitzWith L ψ ∧
      Continuous ψ ∧
      Integrable (fun x => Real.exp (-ψ x)) (volume : Measure E) ∧
      (∫ x, Real.exp (-ψ x) ∂(volume : Measure E)) = 1 ∧
      IsProbabilityMeasure
        (FunctionalInequalities.Probability.MomentMeasure.weightedMeasure (volume : Measure E) (fun x => (ψ x : EReal))) ∧
      ∀ f : E → EReal, FunctionalInequalities.Probability.MomentMeasure.PotentialIntegrable f (μ : Measure E) →
        FunctionalInequalities.Probability.MomentMeasure.variationalFunctional (volume : Measure E) (μ : Measure E) f ≤
          FunctionalInequalities.Probability.MomentMeasure.variationalFunctional (volume : Measure E) (μ : Measure E) q := by
  obtain ⟨q, a, m, ψ, hqconv, hqlsc, hqpot, hqdom, haB, ham, hfloor,
    hfinite, hupper, hdef, hψ, hqmass, hqmax⟩ :=
    FunctionalInequalities.KLS.CEK.bounded_source_finite_conjugate_readable μ hμ L hL
  have hconv : ConvexOn ℝ (univ : Set E) ψ :=
    FunctionalInequalities.Analysis.real_convexOn_legendre_readable q ψ hψ
  have hlip : LipschitzWith L ψ :=
    FunctionalInequalities.Analysis.lipschitzWith_real_legendre_readable q L ψ hqpot.1 hqdom hψ
  obtain ⟨hexp, hint, hprob⟩ :=
    FunctionalInequalities.Probability.MomentMeasure.real_legendre_normalization_readable (volume : Measure E) q ψ hψ hqmass
  exact ⟨q, a, m, ψ, hqconv, hqlsc, hqpot, hqdom, haB, ham, hfloor,
    hfinite, hupper, hdef, hψ, hqmass, hconv, hlip, hlip.continuous,
    hexp, hint, hprob, hqmax⟩
