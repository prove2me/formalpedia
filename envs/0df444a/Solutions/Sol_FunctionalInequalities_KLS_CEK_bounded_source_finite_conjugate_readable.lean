-- Prove2me | solution 1 for FunctionalInequalities.KLS.CEK.bounded_source_finite_conjugate_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:20:45.427141+00:00
-- url     : https://prove2.me/submissions/9062338a-34c9-44f3-be66-59029977519e

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Legendre
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_MomentMeasure_Integrability
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_BoundedConjugate
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_CEK_BoundedPrimal
import Theorems.Thm_FunctionalInequalities_Analysis_convex_epigraph_legendre_readable
import Theorems.Thm_FunctionalInequalities_Analysis_exists_real_global_minimum_of_bounded_domain_readable
import Theorems.Thm_FunctionalInequalities_Analysis_legendre_le_of_real_lower_bound_readable
import Theorems.Thm_FunctionalInequalities_Analysis_legendre_ne_bot_iff_readable
import Theorems.Thm_FunctionalInequalities_KLS_CEK_bounded_source_cap_lsc_readable

section
noncomputable section
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- Conjugation produces a convex potential from precisely a nonempty effective
domain, without any convexity or lower-semicontinuity premise on the primal. -/
theorem FunctionalInequalities.Analysis.convexPotential_legendre (φ : E → EReal) (hfinite : ∃ x, φ x ≠ ⊤) :
    ConvexPotential (legendre φ) :=
  ⟨fun y => (legendre_ne_bot_iff_readable φ y).mpr hfinite, convex_epigraph_legendre_readable φ⟩
end
end
end

section
noncomputable section
section
open FunctionalInequalities.Analysis
section
open MeasureTheory
open scoped ENNReal
section Truncation
variable {E : Type*} [MeasurableSpace E] {μ : MeasureTheory.Measure E}
/-- A nonzero measure and the source a.e. finiteness give a real finite-domain
witness; probability normalization and centering are unnecessary. -/
theorem FunctionalInequalities.Probability.MomentMeasure.potentialIntegrable_exists_finite (f : E → EReal) (hμ : μ ≠ 0)
    (hf : PotentialIntegrable f μ) : ∃ x, f x ≠ ⊤ := by
  let : NeZero μ := ⟨hμ⟩
  exact hf.2.1.exists
end Truncation
end
end
end
end

section
noncomputable section
section
open MeasureTheory Set Metric
open scoped ENNReal Topology RealInnerProductSpace
open FunctionalInequalities
open FunctionalInequalities.Analysis
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Properness excludes bottom for the actual conjugate, and the bounded-slope
upper bound excludes top. No conversion of an infinite value is used. -/
theorem FunctionalInequalities.Analysis.legendre_finite_of_bounded_domain
    (φ : E → EReal) (L : NNReal) (m : ℝ)
    (hbot : ∀ y, φ y ≠ ⊥)
    (hfinite : ∃ y, φ y ≠ ⊤)
    (hdom : ∀ y, φ y ≠ ⊤ → y ∈ closedBall (0 : E) (L : ℝ))
    (hfloor : ∀ y, (m : EReal) ≤ φ y) :
    ∀ x, legendre φ x ≠ ⊤ ∧ legendre φ x ≠ ⊥ := by
  intro x
  refine ⟨?_, (convexPotential_legendre φ hfinite).1 x⟩
  intro htop
  have hu := legendre_le_of_real_lower_bound_readable φ L m hbot hdom hfloor x
  rw [htop] at hu
  exact (not_le_of_gt (EReal.coe_lt_top ((L : ℝ) * ‖x‖ - m))) hu
end
end
end

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
/-- Source-derived compact minimum and globally finite actual conjugate.
The only source inputs are the bundled isotropic probability and its AE norm
bound. The real primal is defined after global finiteness has been established.
This endpoint does not yet assert real convexity, Lipschitz continuity, or the
Bochner exponential-integrability and probability-law bridge. -/
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
      ∀ f : E → EReal, FunctionalInequalities.Probability.MomentMeasure.PotentialIntegrable f (μ : Measure E) →
        FunctionalInequalities.Probability.MomentMeasure.variationalFunctional (volume : Measure E) (μ : Measure E) f ≤
          FunctionalInequalities.Probability.MomentMeasure.variationalFunctional (volume : Measure E) (μ : Measure E) q := by
  classical
  obtain ⟨q, hqconv, hqlsc, hqpot, hqdom, hqmass, hqmax⟩ :=
    FunctionalInequalities.KLS.CEK.bounded_source_cap_lsc_readable μ hμ L hL
  have hμne : (μ : Measure E) ≠ 0 := by
    intro hzero
    have hprob : (μ : Measure E) univ = 1 := measure_univ
    rw [hzero] at hprob
    simp at hprob
  have hqfinite : ∃ y, q y ≠ ⊤ :=
    FunctionalInequalities.Probability.MomentMeasure.potentialIntegrable_exists_finite q hμne hqpot
  obtain ⟨a, haB, m, ham, hfloor⟩ :=
    FunctionalInequalities.Analysis.exists_real_global_minimum_of_bounded_domain_readable
      q L hqpot.1 hqfinite hqlsc hqdom
  have hfinite : ∀ x, FunctionalInequalities.Analysis.legendre q x ≠ ⊤ ∧ FunctionalInequalities.Analysis.legendre q x ≠ ⊥ :=
    FunctionalInequalities.Analysis.legendre_finite_of_bounded_domain q L m hqpot.1 hqfinite hqdom hfloor
  let ψ : E → ℝ := fun x => (FunctionalInequalities.Analysis.legendre q x).toReal
  have hψ : ∀ x, FunctionalInequalities.Analysis.legendre q x = (ψ x : EReal) := by
    intro x
    exact (EReal.coe_toReal (hfinite x).1 (hfinite x).2).symm
  refine ⟨q, a, m, ψ, hqconv, hqlsc, hqpot, hqdom, haB, ham, hfloor,
    hfinite, ?_, rfl, hψ, hqmass, hqmax⟩
  intro x
  exact FunctionalInequalities.Analysis.legendre_le_of_real_lower_bound_readable q L m hqpot.1 hqdom hfloor x
