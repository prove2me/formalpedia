-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.Suspension.jointLaw_eq_tilted_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T17:59:47.097754+00:00
-- url     : https://prove2.me/submissions/65c0e416-91de-4c76-aba7-4a295bff81b6

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Bochner_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Gamma
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Local
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_SquareIntegrable
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coefficients
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coordinate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Multilinear
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Symmetrization
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_BKL_Suspension_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_BKL_Suspension_Law
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_Isotropic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Borel
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_AbsoluteContinuity
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Construction
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Moments
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_FromBorell
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Transport
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_AffineSupport
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_BrunnMinkowski
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Covariance_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Domination_Averages
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Domination_Ball
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Line_BrunnMinkowski
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Line_Laplace
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_LogConcave
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Transport
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic.NoncommRing
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Semicontinuity.Basic
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_Suspension_map_density_shift_scale_408915f
import Theorems.Thm_FunctionalInequalities_Probability_lintegral_pi_prod_fin_408915f

section
noncomputable section
open MeasureTheory Filter Topology InnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
universe u v
section TiltTransport
section MeasurableSpace
variable {A B : Type*}
variable [MeasurableSpace A] [MeasurableSpace B]
/-- Pushing a density through a measurable equivalence: the new density is the old one composed with
the inverse. -/
theorem FunctionalInequalities.Probability.map_withDensity_measurableEquiv
    (e : A ≃ᵐ B) (μ : Measure A) (w : A → ENNReal) (hw : Measurable w) :
    (μ.withDensity w).map e = (μ.map e).withDensity (fun y => w (e.symm y)) := by
  apply Measure.ext_of_lintegral
  intro φ hφ
  rw [lintegral_map hφ e.measurable,
    lintegral_withDensity_eq_lintegral_mul μ hw (show Measurable (fun x => φ (e x)) from hφ.comp e.measurable),
    lintegral_withDensity_eq_lintegral_mul (μ.map e) (show Measurable (fun y => w (e.symm y)) from hw.comp e.symm.measurable) hφ]
  simp only [Pi.mul_apply]
  rw [lintegral_map (show Measurable (fun y => w (e.symm y) * φ y) from (hw.comp e.symm.measurable).mul hφ) e.measurable]
  simp only [e.symm_apply_apply]
end MeasurableSpace
end TiltTransport
end
end
end

open MeasureTheory FunctionalInequalities.Probability.Line
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.KLS
end FunctionalInequalities.KLS
open FunctionalInequalities FunctionalInequalities.KLS
section
namespace FunctionalInequalities.KLS.LogConcave
end FunctionalInequalities.KLS.LogConcave
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.LogConcave
section
namespace FunctionalInequalities.KLS.LogConcave.Suspension
end FunctionalInequalities.KLS.LogConcave.Suspension
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.LogConcave FunctionalInequalities.KLS.LogConcave.Suspension
private theorem FunctionalInequalities.KLS.LogConcave.Suspension.normalized_of_probability_density {A : Type*} [MeasurableSpace A]
    (μ : Measure A) (W : A → ℝ) (hW : Measurable W) {C : ℝ} (hC : 0 < C)
    (hprob : IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (C * Real.exp (W x))))) :
    Integrable (fun x => Real.exp (W x)) μ ∧
      μ.withDensity (fun x => ENNReal.ofReal (C * Real.exp (W x))) = μ.tilted W := by
  let := hprob
  have hmass : ∫⁻ x, ENNReal.ofReal (C * Real.exp (W x)) ∂μ = 1 := by
    have hm := measure_univ (μ := μ.withDensity (fun x => ENNReal.ofReal (C * Real.exp (W x))))
    simpa only [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ] using hm
  have hmeas : Measurable (fun x => C * Real.exp (W x)) := measurable_const.mul hW.exp
  have hnonneg : ∀ x, 0 ≤ C * Real.exp (W x) := fun x => mul_nonneg hC.le (Real.exp_pos _).le
  have hInt : Integrable (fun x => C * Real.exp (W x)) μ := by
    refine ⟨hmeas.aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    simp_rw [Real.enorm_eq_ofReal (hnonneg _)]
    rw [hmass]
    exact ENNReal.one_lt_top
  have hexp : Integrable (fun x => Real.exp (W x)) μ := by
    have ht := hInt.const_mul C⁻¹
    simpa only [← mul_assoc, inv_mul_cancel₀ hC.ne', one_mul] using ht
  have ho : ENNReal.ofReal (∫ x, C * Real.exp (W x) ∂μ) = 1 :=
    (ofReal_integral_eq_lintegral_ofReal hInt (Filter.Eventually.of_forall hnonneg)).trans hmass
  have hval : (∫ x, C * Real.exp (W x) ∂μ) = 1 := by
    exact (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg hnonneg) zero_le_one).1
      (by simpa only [ENNReal.ofReal_one] using ho)
  have hnorm : C * (∫ x, Real.exp (W x) ∂μ) = 1 := by
    rw [← integral_const_mul C]
    exact hval
  have hz : (∫ x, Real.exp (W x) ∂μ) = C⁻¹ := by
    rw [← one_div]
    exact (eq_div_iff hC.ne').2 (by simpa only [mul_comm] using hnorm)
  refine ⟨hexp, ?_⟩
  unfold Measure.tilted
  congr 1
  funext x
  rw [hz, div_eq_mul_inv, inv_inv, mul_comm]
private theorem FunctionalInequalities.KLS.LogConcave.Suspension.piWithDensityOfReal {E : Type*} [MeasurableSpace E]
    (μ : Measure E) [SigmaFinite μ] (ρ : E → ℝ) (hρ : Measurable ρ)
    (_hρnonneg : ∀ x, 0 ≤ ρ x) (N : ℕ) :
    Measure.pi (fun _ : Fin N => μ.withDensity (fun x => ENNReal.ofReal (ρ x))) =
      (Measure.pi (fun _ : Fin N => μ)).withDensity
        (fun x => ∏ i : Fin N, ENNReal.ofReal (ρ (x i))) := by
  classical
  let q : E → ENNReal := fun x => ENNReal.ofReal (ρ x)
  have hq : Measurable q := hρ.ennreal_ofReal
  apply Measure.pi_eq
  intro s hs
  have hrect : MeasurableSet (Set.pi Set.univ s) := MeasurableSet.univ_pi hs
  have hfactor (x : Fin N → E) :
      (Set.pi Set.univ s).indicator (fun x => ∏ i : Fin N, q (x i)) x =
        ∏ i : Fin N, (s i).indicator q (x i) := by
    by_cases hx : x ∈ Set.pi Set.univ s
    · rw [Set.indicator_of_mem hx]
      apply Finset.prod_congr rfl
      intro i hi
      exact (Set.indicator_of_mem (hx i (Set.mem_univ i)) q).symm
    · rw [Set.indicator_of_notMem hx]
      symm
      have hnot : ¬ ∀ i : Fin N, x i ∈ s i := by
        intro hall
        exact hx (fun i _ => hall i)
      obtain ⟨i, hi⟩ := not_forall.mp hnot
      exact Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi q)
  calc
    ((Measure.pi (fun _ : Fin N => μ)).withDensity
        (fun x => ∏ i : Fin N, ENNReal.ofReal (ρ (x i)))) (Set.pi Set.univ s) =
        ∫⁻ x in Set.pi Set.univ s, ∏ i : Fin N, q (x i)
          ∂(Measure.pi (fun _ : Fin N => μ)) := by
            exact withDensity_apply _ hrect
    _ = ∫⁻ x, (Set.pi Set.univ s).indicator (fun x => ∏ i : Fin N, q (x i)) x
          ∂(Measure.pi (fun _ : Fin N => μ)) := (lintegral_indicator hrect _).symm
    _ = ∫⁻ x, ∏ i : Fin N, (s i).indicator q (x i)
          ∂(Measure.pi (fun _ : Fin N => μ)) := lintegral_congr hfactor
    _ = ∏ i : Fin N, ∫⁻ x, (s i).indicator q x ∂μ :=
      Probability.lintegral_pi_prod_fin_408915f μ N (fun i => (s i).indicator q)
        (fun i => hq.indicator (hs i))
    _ = ∏ i : Fin N, (μ.withDensity (fun x => ENNReal.ofReal (ρ x))) (s i) := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [withDensity_apply _ (hs i)]
      exact lintegral_indicator (hs i) q
private theorem FunctionalInequalities.KLS.LogConcave.Suspension.raw_uncurry_volume_preserving (ι κ : Type*) [Fintype ι] [Fintype κ] :
    MeasurePreserving (Function.uncurry : (ι → κ → ℝ) → (ι × κ → ℝ)) volume volume := by
  refine ⟨measurable_uncurry, ?_⟩
  change (Measure.pi fun _ : ι => (Measure.pi fun _ : κ => (volume : Measure ℝ))).map
    Function.uncurry = Measure.pi (fun _ : ι × κ => (volume : Measure ℝ))
  apply (Measure.pi_eq (μ := fun _ : ι × κ => (volume : Measure ℝ)) ?_).symm
  intro s hs
  have he : Function.uncurry ⁻¹' Set.pi Set.univ s =
      Set.pi Set.univ (fun i : ι => Set.pi Set.univ (fun j : κ => s (i, j))) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left,
      Function.uncurry, Prod.forall]
  rw [Measure.map_apply measurable_uncurry (MeasurableSet.univ_pi hs), he, Measure.pi_pi]
  simp only [Measure.pi_pi, Fintype.prod_prod_type]
private theorem FunctionalInequalities.KLS.LogConcave.Suspension.raw_option_volume_preserving (ι : Type*) [Fintype ι] :
    MeasurePreserving (MeasurableEquiv.piOptionEquivProd (fun _ : Option ι => ℝ)).symm
      volume volume := by
  refine ⟨(MeasurableEquiv.piOptionEquivProd (fun _ : Option ι => ℝ)).symm.measurable, ?_⟩
  exact Measure.pi_map_piOptionEquivProd (fun _ : Option ι => (volume : Measure ℝ))
private theorem FunctionalInequalities.KLS.LogConcave.Suspension.raw_assembly_volume_preserving (N n : ℕ) :
    MeasurePreserving
      (fun q : (Fin N → EuclideanSpace ℝ (Fin n)) × ℝ =>
        (WithLp.toLp 2 fun o => Option.elim o q.2 fun ij => q.1 ij.1 ij.2 : JointSpace N n))
      volume volume := by
  let blockOfLp : (Fin N → EuclideanSpace ℝ (Fin n)) → (Fin N → Fin n → ℝ) :=
    fun x i => (x i).ofLp
  have hblock : MeasurePreserving blockOfLp volume volume :=
    volume_preserving_pi (fun _ : Fin N => PiLp.volume_preserving_ofLp (Fin n))
  have hflat : MeasurePreserving (Function.uncurry ∘ blockOfLp) volume volume :=
    (raw_uncurry_volume_preserving (Fin N) (Fin n)).comp hblock
  have hprod : MeasurePreserving
      (Prod.map (Function.uncurry ∘ blockOfLp) (id : ℝ → ℝ)) volume volume := by
    simpa only [← Measure.volume_eq_prod] using
      hflat.prod (MeasurePreserving.id (volume : Measure ℝ))
  have heq :
      (fun q : (Fin N → EuclideanSpace ℝ (Fin n)) × ℝ =>
        (WithLp.toLp 2 fun o => Option.elim o q.2 fun ij => q.1 ij.1 ij.2 : JointSpace N n)) =
      WithLp.toLp 2 ∘
        (MeasurableEquiv.piOptionEquivProd (fun _ : Option (Fin N × Fin n) => ℝ)).symm ∘
          Prod.map (Function.uncurry ∘ blockOfLp) id := by
    funext q
    ext o
    cases o <;> rfl
  rw [heq]
  exact (PiLp.volume_preserving_toLp (Option (Fin N × Fin n))).comp
    ((raw_option_volume_preserving (Fin N × Fin n)).comp hprod)
private theorem FunctionalInequalities.KLS.LogConcave.Suspension.raw_assembly_left_inverse (N n : ℕ)
    (q : (Fin N → EuclideanSpace ℝ (Fin n)) × ℝ) :
    (fun p : JointSpace N n =>
      (fun i : Fin N => WithLp.toLp 2 fun j : Fin n => p (some (i, j)), p none))
      (WithLp.toLp 2 fun o => Option.elim o q.2 fun ij => q.1 ij.1 ij.2) = q := by
  rcases q with ⟨x, s⟩
  apply Prod.ext
  · funext i
    ext j
    rfl
  · rfl
private theorem FunctionalInequalities.KLS.LogConcave.Suspension.raw_assembly_right_inverse (N n : ℕ) (p : JointSpace N n) :
    (fun q : (Fin N → EuclideanSpace ℝ (Fin n)) × ℝ =>
      (WithLp.toLp 2 fun o => Option.elim o q.2 fun ij => q.1 ij.1 ij.2 : JointSpace N n))
      (fun i : Fin N => WithLp.toLp 2 fun j : Fin n => p (some (i, j)), p none) = p := by
  ext o
  cases o <;> rfl
private theorem FunctionalInequalities.KLS.LogConcave.Suspension.raw_assembly_inverse_measurable (N n : ℕ) :
    Measurable (fun p : JointSpace N n =>
      (fun i : Fin N => WithLp.toLp 2 fun j : Fin n => p (some (i, j)), p none)) := by
  fun_prop
/-- Construct the actual measurable equivalence locally, ready for inverse-density transport. -/
private theorem FunctionalInequalities.KLS.LogConcave.Suspension.exists_raw_assembly_equiv (N n : ℕ) :
    ∃ e : ((Fin N → EuclideanSpace ℝ (Fin n)) × ℝ) ≃ᵐ JointSpace N n,
      (∀ q, e q = WithLp.toLp 2 fun o => Option.elim o q.2 fun ij => q.1 ij.1 ij.2) ∧
      (∀ p, e.symm p =
        (fun i : Fin N => WithLp.toLp 2 fun j : Fin n => p (some (i, j)), p none)) ∧
      MeasurePreserving e volume volume := by
  let e : ((Fin N → EuclideanSpace ℝ (Fin n)) × ℝ) ≃ᵐ JointSpace N n :=
    { toEquiv :=
        { toFun := fun q => WithLp.toLp 2 fun o => Option.elim o q.2 fun ij => q.1 ij.1 ij.2
          invFun := fun p =>
            (fun i : Fin N => WithLp.toLp 2 fun j : Fin n => p (some (i, j)), p none)
          left_inv := raw_assembly_left_inverse N n
          right_inv := raw_assembly_right_inverse N n }
      measurable_toFun := (raw_assembly_volume_preserving N n).measurable
      measurable_invFun := raw_assembly_inverse_measurable N n }
  exact ⟨e, fun _ => rfl, fun _ => rfl, raw_assembly_volume_preserving N n⟩
private theorem FunctionalInequalities.KLS.LogConcave.Suspension.joint_density_product {n N : ℕ}
    (V f : EuclideanSpace ℝ (Fin n) → ℝ) {β σ Z : ℝ}
    (hσ : 0 < σ) (hZ : 0 < Z)
    (s : ℝ) (x : Fin N → EuclideanSpace ℝ (Fin n)) :
    ENNReal.ofReal |σ| *
      ((∏ i : Fin N, ENNReal.ofReal (Real.exp (-V (x i)) / Z)) *
        ENNReal.ofReal (laplaceDensity β (σ * s - copyStat f N x))) =
      ENNReal.ofReal ((σ * (β / 2) / Z ^ N) *
        Real.exp (-potential V f β σ N (s, x))) := by
  have hp : 0 ≤ ∏ i : Fin N, Real.exp (-V (x i)) / Z := by positivity
  rw [abs_of_pos hσ,
    ← ENNReal.ofReal_prod_of_nonneg
      (fun (i : Fin N) _ => div_nonneg (Real.exp_pos _).le hZ.le),
    ← ENNReal.ofReal_mul hp, ← ENNReal.ofReal_mul hσ.le]
  congr 1
  have he : (∏ i : Fin N, Real.exp (-V (x i))) =
      Real.exp (-(∑ i : Fin N, V (x i))) := by
    rw [← Real.exp_sum, Finset.sum_neg_distrib]
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, he]
  simp only [laplaceDensity, potential, copyStat, neg_add, Real.exp_add]
  ring
namespace FunctionalInequalities.KLS.LogConcave.Suspension
end FunctionalInequalities.KLS.LogConcave.Suspension
open FunctionalInequalities.KLS.LogConcave.Suspension in
/-- **The density (109).** -/
theorem solution {n N : ℕ} (V f : EuclideanSpace ℝ (Fin n) → ℝ) {β : ℝ} (hβ : 0 < β)
    (hV : Measurable V) (hf : Measurable f) (hint : Integrable (fun x => Real.exp (-V x))) :
    FunctionalInequalities.KLS.LogConcave.Suspension.jointLaw (volume.tilted fun x => -V x) f β (FunctionalInequalities.KLS.LogConcave.Suspension.sigma β) N =
      (volume : Measure (FunctionalInequalities.KLS.LogConcave.Suspension.JointSpace N n)).tilted fun p =>
        -FunctionalInequalities.KLS.LogConcave.Suspension.potential V f β (FunctionalInequalities.KLS.LogConcave.Suspension.sigma β) N (p none, fun i => WithLp.toLp 2 fun j => p (some (i, j))) := by
  classical
  let Z : ℝ := ∫ x, Real.exp (-V x)
  let σ : ℝ := FunctionalInequalities.KLS.LogConcave.Suspension.sigma β
  let μ : Measure (EuclideanSpace ℝ (Fin n)) := volume.tilted (fun x => -V x)
  let ρ : EuclideanSpace ℝ (Fin n) → ℝ := fun x => Real.exp (-V x) / Z
  let H : (Fin N → EuclideanSpace ℝ (Fin n)) → ENNReal :=
    fun x => ∏ i : Fin N, ENNReal.ofReal (ρ (x i))
  let w : ((Fin N → EuclideanSpace ℝ (Fin n)) × ℝ) → ENNReal :=
    fun q => H q.1 * ENNReal.ofReal (FunctionalInequalities.Probability.Line.laplaceDensity β q.2)
  let T : ((Fin N → EuclideanSpace ℝ (Fin n)) × ℝ) →
      ((Fin N → EuclideanSpace ℝ (Fin n)) × ℝ) :=
    fun q => (q.1, (FunctionalInequalities.KLS.LogConcave.Suspension.copyStat f N q.1 + q.2) / σ)
  let wt : ((Fin N → EuclideanSpace ℝ (Fin n)) × ℝ) → ENNReal :=
    fun q => ENNReal.ofReal |σ| * w (q.1, σ * q.2 - FunctionalInequalities.KLS.LogConcave.Suspension.copyStat f N q.1)
  let C : ℝ := σ * (β / 2) / Z ^ N
  let W : FunctionalInequalities.KLS.LogConcave.Suspension.JointSpace N n → ℝ := fun p =>
    -FunctionalInequalities.KLS.LogConcave.Suspension.potential V f β σ N (p none, fun i => WithLp.toLp 2 fun j => p (some (i, j)))
  have hZ : 0 < Z := integral_exp_pos hint
  have hσ : 0 < σ := by dsimp [σ, FunctionalInequalities.KLS.LogConcave.Suspension.sigma]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hρ : Measurable ρ := hV.neg.exp.div_const Z
  have hH : Measurable H := by
    apply Finset.measurable_prod
    intro i _hi
    exact hρ.ennreal_ofReal.comp (measurable_pi_apply i)
  have hη : Measurable (fun s => ENNReal.ofReal (FunctionalInequalities.Probability.Line.laplaceDensity β s)) := by
    unfold FunctionalInequalities.Probability.Line.laplaceDensity
    fun_prop
  have hw : Measurable w := (hH.comp measurable_fst).mul (hη.comp measurable_snd)
  have hF : Measurable (FunctionalInequalities.KLS.LogConcave.Suspension.copyStat f N) := by unfold FunctionalInequalities.KLS.LogConcave.Suspension.copyStat; measurability
  have hT : Measurable T := measurable_fst.prodMk
    (((hF.comp measurable_fst).add measurable_snd).div_const σ)
  have hwt : Measurable wt := measurable_const.mul
    (hw.comp (measurable_fst.prodMk
      ((measurable_const.mul measurable_snd).sub (hF.comp measurable_fst))))
  have hpi : (Measure.pi fun _ : Fin N => μ) =
      (volume : Measure (Fin N → EuclideanSpace ℝ (Fin n))).withDensity H :=
    piWithDensityOfReal volume ρ hρ (fun _ => by dsimp [ρ]; positivity) N
  have hinput : (Measure.pi (fun _ : Fin N => μ)).prod (FunctionalInequalities.Probability.Line.laplaceMeasure β) =
      (volume : Measure ((Fin N → EuclideanSpace ℝ (Fin n)) × ℝ)).withDensity w := by
    rw [hpi, FunctionalInequalities.Probability.Line.laplaceMeasure, prod_withDensity hH hη, ← Measure.volume_eq_prod]
  have hmapT :
      ((volume : Measure ((Fin N → EuclideanSpace ℝ (Fin n)) × ℝ)).withDensity w).map T =
        (volume : Measure ((Fin N → EuclideanSpace ℝ (Fin n)) × ℝ)).withDensity wt := by
    simpa only [Measure.volume_eq_prod] using
      FunctionalInequalities.KLS.LogConcave.Suspension.map_density_shift_scale_408915f (volume : Measure (Fin N → EuclideanSpace ℝ (Fin n)))
        (FunctionalInequalities.KLS.LogConcave.Suspension.copyStat f N) hF σ hσ.ne' w hw
  obtain ⟨e, hef, hei, hevol⟩ := exists_raw_assembly_equiv N n
  have hembed : FunctionalInequalities.KLS.LogConcave.Suspension.embed f σ N = e ∘ T := by
    funext q
    rw [Function.comp_apply, hef]
    rfl
  have hraw : Measurable (fun q : (Fin N → EuclideanSpace ℝ (Fin n)) × ℝ =>
      -FunctionalInequalities.KLS.LogConcave.Suspension.potential V f β σ N (q.2, q.1)) := by
    unfold FunctionalInequalities.KLS.LogConcave.Suspension.potential
    measurability
  have hWeq : W = (fun q : (Fin N → EuclideanSpace ℝ (Fin n)) × ℝ =>
      -FunctionalInequalities.KLS.LogConcave.Suspension.potential V f β σ N (q.2, q.1)) ∘ e.symm := by
    funext p
    rw [Function.comp_apply, hei]
  have hW : Measurable W := hWeq ▸ hraw.comp e.symm.measurable
  have hjoint : FunctionalInequalities.KLS.LogConcave.Suspension.jointLaw μ f β σ N =
      (volume : Measure (FunctionalInequalities.KLS.LogConcave.Suspension.JointSpace N n)).withDensity (fun p => wt (e.symm p)) := by
    rw [FunctionalInequalities.KLS.LogConcave.Suspension.jointLaw, hembed, ← Measure.map_map e.measurable hT, hinput, hmapT,
      FunctionalInequalities.Probability.map_withDensity_measurableEquiv e volume wt hwt, hevol.map_eq]
  have hweight : ∀ p : FunctionalInequalities.KLS.LogConcave.Suspension.JointSpace N n,
      wt (e.symm p) = ENNReal.ofReal (C * Real.exp (W p)) := by
    intro p
    rw [hei]
    exact joint_density_product V f hσ hZ (p none)
      (fun i => WithLp.toLp 2 fun j => p (some (i, j)))
  have hdensity : FunctionalInequalities.KLS.LogConcave.Suspension.jointLaw μ f β σ N =
      (volume : Measure (FunctionalInequalities.KLS.LogConcave.Suspension.JointSpace N n)).withDensity
        (fun p => ENNReal.ofReal (C * Real.exp (W p))) := by
    rw [hjoint]
    congr 1
    funext p
    exact hweight p
  let hpμ : IsProbabilityMeasure μ := isProbabilityMeasure_tilted hint
  have hpjoint : IsProbabilityMeasure (FunctionalInequalities.KLS.LogConcave.Suspension.jointLaw μ f β σ N) :=
    FunctionalInequalities.KLS.LogConcave.Suspension.isProbabilityMeasure_jointLaw_of_pos μ hf hβ σ N
  have hpweight : IsProbabilityMeasure ((volume : Measure (FunctionalInequalities.KLS.LogConcave.Suspension.JointSpace N n)).withDensity
      (fun p => ENNReal.ofReal (C * Real.exp (W p)))) := hdensity ▸ hpjoint
  change FunctionalInequalities.KLS.LogConcave.Suspension.jointLaw μ f β σ N = (volume : Measure (FunctionalInequalities.KLS.LogConcave.Suspension.JointSpace N n)).tilted W
  exact hdensity.trans (normalized_of_probability_density volume W hW hC hpweight).2
