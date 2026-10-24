-- Prove2me | solution 1 for FunctionalInequalities.KLS.CEK.bounded_source_cap_lsc_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:45:41.907989+00:00
-- url     : https://prove2.me/submissions/53b997c8-a3d8-49a8-afec-fcc26e672c7d

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Bochner_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Gamma
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Affine
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_AffineMaximum
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_BoundedConjugate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_RadialExtension
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_Isotropic
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_AffineSupport
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Covariance_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_MomentMeasure_Basic
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.EReal.Operations
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Tactic.NoncommRing
import Mathlib.Topology.Bases
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Theorems.Thm_FunctionalInequalities_Analysis_closedBallCap_lowerSemicontinuous_408915f
import Theorems.Thm_FunctionalInequalities_KLS_CEK_exists_variational_maximum_408915f

section
noncomputable section
open MeasureTheory
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Probability
end FunctionalInequalities.Probability
open FunctionalInequalities FunctionalInequalities.Probability
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E]
/-- The affine support is the smallest closed affine subspace of full measure. -/
theorem FunctionalInequalities.Probability.affineSupport_le_of_ae_mem (μ : ProbabilityMeasure E) (A : AffineSubspace ℝ E)
    (hA : IsClosed (A : Set E)) (hμ : ∀ᵐ x ∂(μ : Measure E), x ∈ A) :
    affineSupport μ ≤ A := by
  apply affineSpan_le.mpr
  exact Measure.support_subset_of_isClosed hA hμ
end
end
end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [MeasurableSpace E] [BorelSpace E]
variable [SecondCountableTopology E] [FiniteDimensional ℝ E]
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Probability
end FunctionalInequalities.Probability
open FunctionalInequalities FunctionalInequalities.Probability
omit [BorelSpace E] in
/-- The barycenter of a probability law with finite second moment lies in its affine support. -/
theorem FunctionalInequalities.Probability.integral_id_mem_affineSupport (μ : ProbabilityMeasure E)
    (hμ : MemLp id 2 (μ : Measure E)) : (∫ x, x ∂(μ : Measure E)) ∈ affineSupport μ :=
  (affineSupport μ).convex.integral_mem (isClosed_affineSupport μ) (ae_mem_affineSupport μ)
    (hμ.integrable (by norm_num))
end
end
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Covariance
end FunctionalInequalities.Covariance
open FunctionalInequalities FunctionalInequalities.Covariance
open Probability
/-- The ambient covariance operator annihilates the orthogonal complement of the direction of the
affine support. -/
theorem FunctionalInequalities.Covariance.operator_apply_eq_zero_of_mem_orthogonal (μ : ProbabilityMeasure E)
    (hμ : MemLp id 2 (μ : Measure E)) {w : E} (hw : w ∈ (affineSupport μ).directionᗮ) :
    operator (μ : Measure E) w = 0 := by
  apply ext_inner_right ℝ
  intro y
  rw [operator_inner, inner_zero_left, covarianceBilin_apply hμ]
  have hm : (∫ x, id x ∂(μ : Measure E)) ∈ affineSupport μ := integral_id_mem_affineSupport μ hμ
  refine integral_eq_zero_of_ae ?_
  filter_upwards [ae_mem_affineSupport μ] with z hz
  have hdir : z - ∫ x, id x ∂(μ : Measure E) ∈ (affineSupport μ).direction :=
    AffineSubspace.vsub_mem_direction hz hm
  show inner ℝ w (z - ∫ x, id x ∂(μ : Measure E)) * inner ℝ y (z - ∫ x, id x ∂(μ : Measure E)) = 0
  rw [Submodule.inner_left_of_mem_orthogonal hdir hw, zero_mul]
end
end
end
end

section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
/-- An injective covariance operator forces full affine support. -/
theorem FunctionalInequalities.Probability.affineSupport_eq_top_of_covariance_injective (μ : ProbabilityMeasure E)
    (h2 : MemLp id 2 (μ : Measure E)) (hinj : Function.Injective (Covariance.operator (μ : Measure E))) :
    Probability.affineSupport μ = ⊤ := by
  have hperp : (Probability.affineSupport μ).directionᗮ = ⊥ := by
    apply bot_unique
    intro w hw
    have h := Covariance.operator_apply_eq_zero_of_mem_orthogonal μ h2 hw
    have hz : w = 0 := hinj (h.trans (map_zero _).symm)
    simpa only [Submodule.mem_bot] using hz
  have hdir : (Probability.affineSupport μ).direction = ⊤ := Submodule.orthogonal_eq_bot_iff.mp hperp
  have hne : (Probability.affineSupport μ : Set E).Nonempty :=
    ⟨Probability.origin μ, (Probability.origin μ).property⟩
  exact (AffineSubspace.direction_eq_top_iff_of_nonempty hne).mp hdir
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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- The Legendre transform reverses pointwise order, including extended values. -/
theorem FunctionalInequalities.Analysis.legendre_antitone {φ ψ : E → EReal} (h : ∀ x, φ x ≤ ψ x) (y : E) :
    legendre ψ y ≤ legendre φ y := by
  apply iSup_le
  intro x
  exact (EReal.sub_le_sub le_rfl (h x)).trans
    (le_iSup (fun z : E => (inner ℝ z y : EReal) - φ z) x)
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
open MeasureTheory
open scoped ENNReal
open FunctionalInequalities.Analysis
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
section Measurable
variable [MeasurableSpace E]
/-- The monotonicity used for the truncation in CEK (61): increasing the primal
potential increases the mass of the exponential of its negative Legendre transform. -/
theorem FunctionalInequalities.Probability.MomentMeasure.mass_legendre_mono (dx : Measure E) {φ ψ : E → EReal} (h : ∀ x, φ x ≤ ψ x) :
    mass dx (legendre φ) ≤ mass dx (legendre ψ) := by
  apply lintegral_mono
  intro x
  exact EReal.exp_monotone (EReal.neg_le_neg_iff.mpr (legendre_antitone h x))
end Measurable
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
open MeasureTheory Set Metric
open scoped ENNReal Topology RealInnerProductSpace
open FunctionalInequalities
open FunctionalInequalities.Analysis
open FunctionalInequalities.KLS
open FunctionalInequalities.Probability
open FunctionalInequalities.Probability.MomentMeasure
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
namespace FunctionalInequalities.KLS.CEK
end FunctionalInequalities.KLS.CEK
open FunctionalInequalities.KLS.CEK in
/-- Strengthening of the cap-only source construction. The LSC input for the
cap helper is obtained from this very CEK optimizer, not supplied by the caller.
The original admissibility, mass-one and all-competitor conclusions are retained. -/
theorem solution
    (μ : ProbabilityMeasure E) (hμ : FunctionalInequalities.KLS.Isotropic μ) (L : NNReal)
    (hL : ∀ᵐ y ∂(μ : Measure E), ‖y‖ ≤ (L : ℝ)) :
    ∃ q : E → EReal,
      FunctionalInequalities.Analysis.ConvexPotential q ∧
      LowerSemicontinuous q ∧
      FunctionalInequalities.Probability.MomentMeasure.PotentialIntegrable q (μ : Measure E) ∧
      (∀ y, q y ≠ ⊤ → y ∈ closedBall (0 : E) (L : ℝ)) ∧
      FunctionalInequalities.Probability.MomentMeasure.mass (volume : Measure E) (FunctionalInequalities.Analysis.legendre q) = 1 ∧
      ∀ f : E → EReal, FunctionalInequalities.Probability.MomentMeasure.PotentialIntegrable f (μ : Measure E) →
        FunctionalInequalities.Probability.MomentMeasure.variationalFunctional (volume : Measure E) (μ : Measure E) f ≤
          FunctionalInequalities.Probability.MomentMeasure.variationalFunctional (volume : Measure E) (μ : Measure E) q := by
  classical
  have hfirst : Integrable (fun x : E => x) (μ : Measure E) :=
    hμ.memLp_two.integrable (by norm_num)
  have hinj : Function.Injective (FunctionalInequalities.Covariance.operator (μ : Measure E)) := by
    intro x y hxy
    rw [hμ.covariance_identity] at hxy
    simpa only [ContinuousLinearMap.id_apply] using hxy
  have hsub :
      ∀ V : Submodule ℝ E, (μ : Measure E) (V : Set E)ᶜ = 0 → V = ⊤ := by
    intro V hV
    have hfull : FunctionalInequalities.Probability.affineSupport μ = ⊤ :=
      FunctionalInequalities.Probability.affineSupport_eq_top_of_covariance_injective μ hμ.memLp_two hinj
    let A : AffineSubspace ℝ E := AffineSubspace.mk' (0 : E) V
    have hAe : ∀ᵐ x ∂(μ : Measure E), x ∈ A := by
      filter_upwards [hV] with x hx
      simpa [A, AffineSubspace.mem_mk'] using hx
    have hle : FunctionalInequalities.Probability.affineSupport μ ≤ A :=
      FunctionalInequalities.Probability.affineSupport_le_of_ae_mem μ A A.closed_of_finiteDimensional hAe
    have hAtop : A = ⊤ := by
      rw [hfull] at hle
      exact top_unique hle
    apply top_unique
    intro x hx
    have hxA : x ∈ A := by
      rw [hAtop]
      trivial
    simpa [A, AffineSubspace.mem_mk'] using hxA
  obtain ⟨q0, hq0conv, hq0lsc, hq0pot, hq0mass, hq0max⟩ :=
    FunctionalInequalities.KLS.CEK.exists_variational_maximum_408915f
      (volume : Measure E) (μ : Measure E) hsub hfirst hμ.mean_zero
  let q : E → EReal := FunctionalInequalities.Analysis.closedBallCap q0 L
  have hqlsc : LowerSemicontinuous q :=
    FunctionalInequalities.Analysis.closedBallCap_lowerSemicontinuous_408915f q0 L hq0lsc
  have hqeq : q =ᵐ[(μ : Measure E)] q0 := by
    filter_upwards [hL] with y hy
    have hyB : y ∈ closedBall (0 : E) (L : ℝ) := by
      simpa [mem_closedBall] using hy
    simp [q, FunctionalInequalities.Analysis.closedBallCap, hyB]
  have hqconv : FunctionalInequalities.Analysis.ConvexPotential q := by
    refine ⟨?_, ?_⟩
    · intro x
      by_cases hx : x ∈ closedBall (0 : E) (L : ℝ)
      · simpa [q, FunctionalInequalities.Analysis.closedBallCap, hx] using hq0conv.1 x
      · simp [q, FunctionalInequalities.Analysis.closedBallCap, hx]
    · intro p hp r hr a b ha hb hab
      have hpB : p.1 ∈ closedBall (0 : E) (L : ℝ) := by
        by_contra hpB
        have htop : (⊤ : EReal) ≤ (p.2 : EReal) := by
          change
            (if p.1 ∈ closedBall (0 : E) (L : ℝ) then q0 p.1 else ⊤) ≤
              (p.2 : EReal) at hp
          rw [if_neg hpB] at hp
          exact hp
        exact (not_le_of_gt (EReal.coe_lt_top p.2)) htop
      have hrB : r.1 ∈ closedBall (0 : E) (L : ℝ) := by
        by_contra hrB
        have htop : (⊤ : EReal) ≤ (r.2 : EReal) := by
          change
            (if r.1 ∈ closedBall (0 : E) (L : ℝ) then q0 r.1 else ⊤) ≤
              (r.2 : EReal) at hr
          rw [if_neg hrB] at hr
          exact hr
        exact (not_le_of_gt (EReal.coe_lt_top r.2)) htop
      have hp0 : q0 p.1 ≤ (p.2 : EReal) := by
        change
          (if p.1 ∈ closedBall (0 : E) (L : ℝ) then q0 p.1 else ⊤) ≤
            (p.2 : EReal) at hp
        rw [if_pos hpB] at hp
        exact hp
      have hr0 : q0 r.1 ≤ (r.2 : EReal) := by
        change
          (if r.1 ∈ closedBall (0 : E) (L : ℝ) then q0 r.1 else ⊤) ≤
            (r.2 : EReal) at hr
        rw [if_pos hrB] at hr
        exact hr
      have habB : a • p.1 + b • r.1 ∈ closedBall (0 : E) (L : ℝ) :=
        (convex_closedBall (0 : E) (L : ℝ)) hpB hrB ha hb hab
      change
        (if a • p.1 + b • r.1 ∈ closedBall (0 : E) (L : ℝ) then
            q0 (a • p.1 + b • r.1)
          else ⊤) ≤
          (↑a : EReal) * ↑p.2 + (↑b : EReal) * ↑r.2
      rw [if_pos habB]
      exact hq0conv.2 hp0 hr0 ha hb hab
  have hqpot : FunctionalInequalities.Probability.MomentMeasure.PotentialIntegrable q (μ : Measure E) := by
    refine ⟨?_, ?_, ?_⟩
    · intro x
      by_cases hx : x ∈ closedBall (0 : E) (L : ℝ)
      · simpa [q, FunctionalInequalities.Analysis.closedBallCap, hx] using hq0conv.1 x
      · simp [q, FunctionalInequalities.Analysis.closedBallCap, hx]
    · filter_upwards [hqeq, hq0pot.2.1] with x hx hxf
      rw [hx]
      exact hxf
    · have hto :
          (fun x => (q x).toReal) =ᵐ[(μ : Measure E)]
            (fun x => (q0 x).toReal) := by
        filter_upwards [hqeq] with x hx
        rw [hx]
      exact hq0pot.2.2.congr hto.symm
  have hqdom : ∀ y, q y ≠ ⊤ → y ∈ closedBall (0 : E) (L : ℝ) := by
    intro y hy
    by_contra hyB
    apply hy
    simp [q, FunctionalInequalities.Analysis.closedBallCap, hyB]
  have hqle : ∀ x, q0 x ≤ q x := by
    intro x
    by_cases hx : x ∈ closedBall (0 : E) (L : ℝ)
    · simp [q, FunctionalInequalities.Analysis.closedBallCap, hx]
    · simp [q, FunctionalInequalities.Analysis.closedBallCap, hx]
  have hmassmono :
      FunctionalInequalities.Probability.MomentMeasure.mass (volume : Measure E) (FunctionalInequalities.Analysis.legendre q0) ≤
        FunctionalInequalities.Probability.MomentMeasure.mass (volume : Measure E) (FunctionalInequalities.Analysis.legendre q) :=
    FunctionalInequalities.Probability.MomentMeasure.mass_legendre_mono (volume : Measure E) hqle
  have hqint :
      (∫ x, (q x).toReal ∂(μ : Measure E)) =
        ∫ x, (q0 x).toReal ∂(μ : Measure E) := by
    have hto :
        (fun x => (q x).toReal) =ᵐ[(μ : Measure E)]
          (fun x => (q0 x).toReal) := by
      filter_upwards [hqeq] with x hx
      rw [hx]
    exact integral_congr_ae hto
  have hmassq : FunctionalInequalities.Probability.MomentMeasure.mass (volume : Measure E) (FunctionalInequalities.Analysis.legendre q) = 1 := by
    have hupper := hq0max q hqpot
    unfold FunctionalInequalities.Probability.MomentMeasure.variationalFunctional at hupper
    rw [hqint, hq0mass, ENNReal.log_one] at hupper
    have hlogupper :
        ENNReal.log (FunctionalInequalities.Probability.MomentMeasure.mass (volume : Measure E) (FunctionalInequalities.Analysis.legendre q)) ≤ 0 := by
      let I : ℝ := ∫ x, (q0 x).toReal ∂(μ : Measure E)
      have hcancel :
          ENNReal.log (FunctionalInequalities.Probability.MomentMeasure.mass (volume : Measure E) (FunctionalInequalities.Analysis.legendre q)) + ((-I : ℝ) : EReal) ≤
            (0 : EReal) + ((-I : ℝ) : EReal) := by
        simpa only [sub_eq_add_neg, EReal.coe_neg, I] using hupper
      exact (EReal.addLECancellable_coe (-I)).add_le_add_iff_right.mp hcancel
    have hloglower :
        0 ≤ ENNReal.log (FunctionalInequalities.Probability.MomentMeasure.mass (volume : Measure E) (FunctionalInequalities.Analysis.legendre q)) := by
      have h := ENNReal.log_monotone hmassmono
      rw [hq0mass, ENNReal.log_one] at h
      exact h
    apply ENNReal.log_injective
    apply le_antisymm
    · simpa only [ENNReal.log_one] using hlogupper
    · simpa only [ENNReal.log_one] using hloglower
  have hqmax :
      ∀ f : E → EReal, FunctionalInequalities.Probability.MomentMeasure.PotentialIntegrable f (μ : Measure E) →
        FunctionalInequalities.Probability.MomentMeasure.variationalFunctional (volume : Measure E) (μ : Measure E) f ≤
          FunctionalInequalities.Probability.MomentMeasure.variationalFunctional (volume : Measure E) (μ : Measure E) q := by
    intro f hf
    have hf0 := hq0max f hf
    have hq0eq :
        FunctionalInequalities.Probability.MomentMeasure.variationalFunctional (volume : Measure E) (μ : Measure E) q =
          FunctionalInequalities.Probability.MomentMeasure.variationalFunctional (volume : Measure E) (μ : Measure E) q0 := by
      unfold FunctionalInequalities.Probability.MomentMeasure.variationalFunctional
      rw [hmassq, hq0mass, hqint]
    rw [hq0eq]
    exact hf0
  exact ⟨q, hqconv, hqlsc, hqpot, hqdom, hmassq, hqmax⟩
