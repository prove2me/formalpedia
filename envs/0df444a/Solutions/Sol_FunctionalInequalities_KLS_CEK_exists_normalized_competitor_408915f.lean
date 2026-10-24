-- Prove2me | solution 1 for FunctionalInequalities.KLS.CEK.exists_normalized_competitor_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:29:06.072194+00:00
-- url     : https://prove2.me/submissions/932bc1fa-0b9d-4465-8d75-dbe69dad4a65

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Affine
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_AffineMaximum
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_MomentMeasure_Basic
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.Data.EReal.Operations
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Semicontinuity.Basic
import Theorems.Thm_FunctionalInequalities_Analysis_exists_nonnegative_origin_zero_affine_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_legendre_affineSubtract_408915f
import Theorems.Thm_FunctionalInequalities_Probability_MomentMeasure_affineSubtract_potentialIntegrable_408915f
import Theorems.Thm_FunctionalInequalities_Probability_MomentMeasure_exists_convexified_lowerTruncate_variational_le_add_408915f
import Theorems.Thm_FunctionalInequalities_Probability_MomentMeasure_integral_affineSubtract_408915f
import Theorems.Thm_FunctionalInequalities_Probability_MomentMeasure_origin_mem_interior_domain_of_lower_bound_408915f
import Theorems.Thm_FunctionalInequalities_Probability_zero_mem_interior_convexHull_support_of_integral_eq_zero_408915f

section
noncomputable section
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- A real lower bound on the primal gives a finite upper bound for its
Legendre transform at zero. This is the normalization used after CEK (61). -/
theorem FunctionalInequalities.Analysis.legendre_zero_le_of_lower_bound (φ : E → EReal) (M : ℝ)
    (h : ∀ x, ((-M : ℝ) : EReal) ≤ φ x) : legendre φ 0 ≤ (M : EReal) := by
  apply iSup_le
  intro x
  simp only [inner_zero_right, EReal.coe_zero, zero_sub]
  apply EReal.neg_le.mpr
  simpa only [EReal.coe_neg] using h x
/-- The CEK lower bound persists through biconjugation. -/
theorem FunctionalInequalities.Analysis.lower_bound_biconjugate (φ : E → EReal) (M : ℝ)
    (hlower : ∀ x, ((-M : ℝ) : EReal) ≤ φ x) (x : E) :
    ((-M : ℝ) : EReal) ≤ legendre (legendre φ) x := by
  have hzero := legendre_zero_le_of_lower_bound φ M hlower
  have hneg : ((-M : ℝ) : EReal) ≤ -legendre φ 0 := by
    simpa only [EReal.coe_neg] using (EReal.neg_le_neg_iff.mpr hzero)
  have hterm : -legendre φ 0 ≤ legendre (legendre φ) x := by
    change -legendre φ 0 ≤ ⨆ z : E, (inner ℝ z x : EReal) - legendre φ z
    simpa only [inner_zero_left, EReal.coe_zero, zero_sub] using
      (le_iSup (fun z : E => (inner ℝ z x : EReal) - legendre φ z) 0)
  exact hneg.trans hterm
end
end
end
end

section
noncomputable section
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- Finite real shifts cancel even when the logarithm is infinite. -/
theorem FunctionalInequalities.Analysis.sub_coe_cancel_shift (z : EReal) (A b : ℝ) :
    (z - (b : EReal)) - ((A - b : ℝ) : EReal) = z - (A : EReal) := by
  induction z with
  | bot => simp
  | top => rw [EReal.top_sub_coe b, EReal.top_sub_coe (A - b), EReal.top_sub_coe A]
  | coe z =>
    norm_cast
    ring
end
end
end
end
end

section
noncomputable section
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Probability
end FunctionalInequalities.Probability
open FunctionalInequalities FunctionalInequalities.Probability
section
namespace FunctionalInequalities.Probability.MomentMeasure
end FunctionalInequalities.Probability.MomentMeasure
open FunctionalInequalities FunctionalInequalities.Probability FunctionalInequalities.Probability.MomentMeasure
open FunctionalInequalities.Analysis
section
open MeasureTheory
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [MeasurableSpace E] [BorelSpace E]
/-- The actual translated conjugate mass for a right-translation-invariant
background measure, retaining both zero and infinite values. -/
theorem FunctionalInequalities.Probability.MomentMeasure.mass_legendre_affineSubtract (dx : Measure E) [Measure.IsAddRightInvariant dx]
    (f : E → EReal) (a : E) (b : ℝ) :
    mass dx (legendre (affineSubtract f a b)) =
      EReal.exp ((-b : ℝ) : EReal) * mass dx (legendre f) := by
  have hneg (x : E) :
      -(legendre f (x + a) + (b : EReal)) =
        -legendre f (x + a) + ((-b : ℝ) : EReal) := by
    simpa only [sub_eq_add_neg, EReal.coe_neg] using
      (EReal.neg_add (.inr (EReal.coe_ne_top b)) (.inr (EReal.coe_ne_bot b)))
  unfold mass density
  simp_rw [legendre_affineSubtract_408915f, hneg, EReal.exp_add]
  rw [lintegral_mul_const' _ _ (by simp)]
  rw [lintegral_add_right_eq_self (μ := dx) (fun y : E => EReal.exp (-legendre f y)) a]
  exact mul_comm _ _
end
section
open MeasureTheory
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E}
omit [BorelSpace E] in
/-- On a centered probability measure, the linear integral vanishes and the
constant contributes exactly its value, rather than total-mass times its value. -/
theorem FunctionalInequalities.Probability.MomentMeasure.integral_affineSubtract_of_probability [CompleteSpace E] [IsProbabilityMeasure μ]
    (f : E → EReal) (a : E) (b : ℝ) (hf : PotentialIntegrable f μ)
    (hfirst : Integrable (fun x : E => x) μ) (hbar : (∫ x, x ∂μ) = 0) :
    (∫ x, (affineSubtract f a b x).toReal ∂μ) = (∫ x, (f x).toReal ∂μ) - b := by
  have hlin : (∫ x, inner ℝ a x ∂μ) = 0 := by
    simpa only [innerSL_apply_apply, hbar, map_zero] using (innerSL ℝ a).integral_comp_comm hfirst
  simpa [hlin] using integral_affineSubtract_408915f f a b hf hfirst
/-- Exact extended logarithm correction for the actual conjugate mass. -/
theorem FunctionalInequalities.Probability.MomentMeasure.log_mass_legendre_affineSubtract (dx : Measure E) [Measure.IsAddRightInvariant dx]
    (f : E → EReal) (a : E) (b : ℝ) :
    ENNReal.log (mass dx (legendre (affineSubtract f a b))) =
      ENNReal.log (mass dx (legendre f)) - (b : EReal) := by
  rw [mass_legendre_affineSubtract, ENNReal.log_mul_add, EReal.log_exp, EReal.coe_neg]
  rw [add_comm]
  rfl
/-- CEK's functional is invariant under the actual affine subtraction for a
centered probability measure, retaining zero/infinite exponential mass. -/
theorem FunctionalInequalities.Probability.MomentMeasure.variationalFunctional_affineSubtract [CompleteSpace E] [IsProbabilityMeasure μ]
    (dx : Measure E) [Measure.IsAddRightInvariant dx]
    (f : E → EReal) (a : E) (b : ℝ) (hf : PotentialIntegrable f μ)
    (hfirst : Integrable (fun x : E => x) μ) (hbar : (∫ x, x ∂μ) = 0) :
    variationalFunctional dx μ (affineSubtract f a b) = variationalFunctional dx μ f := by
  unfold variationalFunctional
  rw [log_mass_legendre_affineSubtract, integral_affineSubtract_of_probability f a b hf hfirst hbar]
  exact sub_coe_cancel_shift _ _ b
end
section
open MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [MeasurableSpace E] [BorelSpace E] {μ : Measure E}
/-- The actual source affine normalization preserves admissibility and the
variational value under the source probability, first-moment and centering data. -/
theorem FunctionalInequalities.Probability.MomentMeasure.exists_origin_zero_affine_of_probability [FiniteDimensional ℝ E] [IsProbabilityMeasure μ]
    (dx : Measure E) [Measure.IsAddRightInvariant dx]
    (f : E → EReal) (hf : PotentialIntegrable f μ) (hconv : ConvexPotential f)
    (h0 : (0 : E) ∈ interior {x | f x ≠ ⊤})
    (hfirst : Integrable (fun x : E => x) μ) (hbar : (∫ x, x ∂μ) = 0) :
    ∃ a : E, let g := affineSubtract f a (f 0).toReal
      ConvexPotential g ∧ PotentialIntegrable g μ ∧ (∀ x, 0 ≤ g x) ∧ g 0 = 0 ∧
        variationalFunctional dx μ g = variationalFunctional dx μ f := by
  obtain ⟨a, hc, hnn, hg0⟩ := exists_nonnegative_origin_zero_affine_408915f f hconv h0
  refine ⟨a, hc, affineSubtract_potentialIntegrable_408915f f a (f 0).toReal hf hfirst, hnn, hg0, ?_⟩
  exact variationalFunctional_affineSubtract dx f a (f 0).toReal hf hfirst hbar
end
end
end
end
end
end

noncomputable section
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.KLS
end FunctionalInequalities.KLS
open FunctionalInequalities FunctionalInequalities.KLS
section
namespace FunctionalInequalities.KLS.CEK
end FunctionalInequalities.KLS.CEK
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.CEK
open FunctionalInequalities.Analysis
open FunctionalInequalities.Probability
open FunctionalInequalities.Probability.MomentMeasure
section
open MeasureTheory Filter Set
open scoped ENNReal Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
namespace FunctionalInequalities.KLS.CEK
end FunctionalInequalities.KLS.CEK
open FunctionalInequalities.KLS.CEK in
/-- Actual reduction of every admissible source competitor: truncate, take the
actual biconjugate, derive its domain interior, produce a touching plane and
subtract it. Every normalization and the epsilon value comparison is proved. -/
theorem solution (dx μ : Measure E) [dx.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (hsub : ∀ V : Submodule ℝ E, μ (V : Set E)ᶜ = 0 → V = ⊤)
    (hfirst : Integrable (fun x : E => x) μ) (hbar : ∫ x, x ∂μ = 0)
    (f : E → EReal) (hf : FunctionalInequalities.Probability.MomentMeasure.PotentialIntegrable f μ) (ε : ℝ) (hε : 0 < ε) :
    ∃ ψ : E → EReal, FunctionalInequalities.Analysis.ConvexPotential ψ ∧ FunctionalInequalities.Probability.MomentMeasure.PotentialIntegrable ψ μ ∧
      (∀ x, 0 ≤ ψ x) ∧ ψ 0 = 0 ∧
      FunctionalInequalities.Probability.MomentMeasure.variationalFunctional dx μ f ≤ FunctionalInequalities.Probability.MomentMeasure.variationalFunctional dx μ ψ + (ε : EReal) := by
  have hμ : μ ≠ 0 := by
    intro hz
    have hu : μ univ = 1 := measure_univ
    simp only [hz, Measure.coe_zero, Pi.zero_apply, zero_ne_one] at hu
  have h0 := FunctionalInequalities.Probability.zero_mem_interior_convexHull_support_of_integral_eq_zero_408915f
    μ hμ hsub hfirst hbar
  obtain ⟨n, _hn, hc, _hls, hp, hvalue⟩ :=
    FunctionalInequalities.Probability.MomentMeasure.exists_convexified_lowerTruncate_variational_le_add_408915f dx f hμ hf ε hε
  let c := FunctionalInequalities.Analysis.legendre (FunctionalInequalities.Analysis.legendre (FunctionalInequalities.Analysis.lowerTruncate f (n : ℝ)))
  have hlower : ∀ x, ((-(n : ℝ) : ℝ) : EReal) ≤ c x :=
    FunctionalInequalities.Analysis.lower_bound_biconjugate _ (n : ℝ) (fun _ => le_max_right _ _)
  have hD := FunctionalInequalities.Probability.MomentMeasure.origin_mem_interior_domain_of_lower_bound_408915f μ h0 hfirst c hc hp (n : ℝ) hlower
  obtain ⟨a, hconv, hpot, hnn, hzero, heq⟩ :=
    FunctionalInequalities.Probability.MomentMeasure.exists_origin_zero_affine_of_probability dx c hp hc hD hfirst hbar
  refine ⟨FunctionalInequalities.Analysis.affineSubtract c a (c 0).toReal, hconv, hpot, hnn, hzero, ?_⟩
  rwa [heq]
