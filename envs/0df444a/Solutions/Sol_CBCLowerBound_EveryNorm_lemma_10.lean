-- Prove2me | solution 1 for CBCLowerBound.EveryNorm.lemma_10
-- status  : ACCEPTED   (prove)
-- author  : @nhc
-- created : 2026-11-13T13:39:09.097306+00:00
-- url     : https://prove2.me/submissions/6f99b514-20dd-4e67-982a-e0703b183a1a

import Definitions.Def_CBCCompactChasingModel
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.Order.GroupWithZero.Finset
import Mathlib.Algebra.Order.Ring.GeomSum
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.NNNorm
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.List.Forall2
import Mathlib.Data.Matrix.Bilinear
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.Lattice

set_option autoImplicit false

namespace CBCProve2MeProofs.Milman
open ConvexBodyChasing

/- Component source: ConvexBodyChasing.GaussianCoordinates -/
section BundledModule059
/-! # Standard finite Gaussian coordinates for the geometric proof

The measure is the actual product of centered, variance-one real Gaussians.
It has full support, and its identity random vector has finite second moment.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace ConvexBodyChasing

variable (ι : Type*) [Fintype ι]

def coordinateGaussian : Measure (ι → ℝ) :=
  Measure.pi (fun _ : ι => gaussianReal 0 1)

instance coordinateGaussian_probability : IsProbabilityMeasure (coordinateGaussian ι) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : ι => gaussianReal 0 1)))

instance coordinateGaussian_openPos : (coordinateGaussian ι).IsOpenPosMeasure := by
  letI : (gaussianReal 0 1).IsOpenPosMeasure :=
    (gaussianReal_absolutelyContinuous' 0 (one_ne_zero : (1 : ℝ≥0) ≠ 0)).isOpenPosMeasure
  exact inferInstanceAs ((Measure.pi (fun _ : ι => gaussianReal 0 1)).IsOpenPosMeasure)

theorem coordinateGaussian_eval (i : ι) :
    MeasurePreserving (fun x : ι → ℝ => x i) (coordinateGaussian ι) (gaussianReal 0 1) :=
  measurePreserving_eval (fun _ : ι => gaussianReal 0 1) i

/-- The standard Gaussian vector has finite second moment. -/
theorem coordinateGaussian_memLp_id : MemLp (id : (ι → ℝ) → (ι → ℝ)) 2
    (coordinateGaussian ι) := by
  apply MemLp.of_eval
  exact fun i => (memLp_id_gaussianReal (μ := 0) (v := 1) 2).comp_measurePreserving
    (coordinateGaussian_eval ι i)

end ConvexBodyChasing

end
end BundledModule059

/- Component source: ConvexBodyChasing.GaussianMoments -/
section BundledModule060
/-! # Independence and covariance of the standard Gaussian coordinates

These facts connect the concrete product measure with Mathlib's Gaussian-law
and covariance APIs for constructing the Gaussian noise operator.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators

namespace ConvexBodyChasing

variable (ι : Type*) [Fintype ι]

theorem coordinateGaussian_independent :
    iIndepFun (fun i (x : ι → ℝ) => x i) (coordinateGaussian ι) :=
  iIndepFun_pi (fun _ : ι => measurable_id.aemeasurable)

instance coordinateGaussian_gaussian : IsGaussian (coordinateGaussian ι) := by
  have h : HasGaussianLaw (id : (ι → ℝ) → (ι → ℝ)) (coordinateGaussian ι) :=
    iIndepFun.hasGaussianLaw
      (fun i => (coordinateGaussian_eval ι i).hasLaw.hasGaussianLaw)
      (coordinateGaussian_independent ι)
  simpa using! h.isGaussian_map

theorem coordinateGaussian_mean (i : ι) : ∫ x, x i ∂coordinateGaussian ι = 0 :=
  (coordinateGaussian_eval ι i).hasLaw.integral_eq.trans integral_id_gaussianReal

theorem coordinateGaussian_integral_id : ∫ x : ι → ℝ, x ∂coordinateGaussian ι = 0 := by
  ext i
  simpa using! ((ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).integral_comp_comm
    ((coordinateGaussian_memLp_id ι).integrable (by norm_num))).symm.trans
      (coordinateGaussian_mean ι i)

theorem coordinateGaussian_variance (i : ι) :
    variance (fun x : ι → ℝ => x i) (coordinateGaussian ι) = 1 :=
  ((coordinateGaussian_eval ι i).variance_fun_comp (f := id)
    measurable_id.aemeasurable).trans variance_id_gaussianReal

theorem coordinateGaussian_covariance_zero {i j : ι} (hij : i ≠ j) :
    covariance (fun x : ι → ℝ => x i) (fun x => x j) (coordinateGaussian ι) = 0 :=
  ((coordinateGaussian_independent ι).indepFun hij).covariance_eq_zero
    ((coordinateGaussian_memLp_id ι).eval i) ((coordinateGaussian_memLp_id ι).eval j)

theorem coordinateGaussian_covariance [DecidableEq ι] (i j : ι) :
    covariance (fun x : ι → ℝ => x i) (fun x => x j) (coordinateGaussian ι) =
      if i = j then 1 else 0 := by
  by_cases hij : i = j
  · simpa [hij, covariance_self (X := fun x : ι → ℝ => x j)
      (measurable_pi_apply j).aemeasurable] using!
      coordinateGaussian_variance ι j
  · simpa [hij] using! coordinateGaussian_covariance_zero ι hij

/-- The covariance form of the standard product Gaussian is the Euclidean dot product. -/
theorem coordinateGaussian_covariance_linear (a b : ι → ℝ) :
    covariance (fun x : ι → ℝ => ∑ i, a i * x i) (fun x => ∑ i, b i * x i)
      (coordinateGaussian ι) = ∑ i, a i * b i := by
  refine (covariance_fun_sum_fun_sum
    (fun i => ((coordinateGaussian_memLp_id ι).eval i).const_mul (a i))
    (fun i => ((coordinateGaussian_memLp_id ι).eval i).const_mul (b i))).trans ?_
  classical
  simp [covariance_const_mul_left, covariance_const_mul_right, coordinateGaussian_covariance,
    mul_comm]

theorem coordinateGaussian_mean_linear (a : ι → ℝ) :
    ∫ x, ∑ i, a i * x i ∂coordinateGaussian ι = 0 := by
  refine (integral_finset_sum Finset.univ (fun i _ =>
    (((coordinateGaussian_memLp_id ι).eval i).integrable (by norm_num)).const_mul (a i))).trans ?_
  simp [integral_const_mul, coordinateGaussian_mean]

theorem coordinateGaussian_variance_linear (a : ι → ℝ) :
    variance (fun x : ι → ℝ => ∑ i, a i * x i) (coordinateGaussian ι) =
      ∑ i, a i ^ 2 := by
  rw [← covariance_self (X := fun x : ι → ℝ => ∑ i, a i * x i)
    (show Measurable (fun x : ι → ℝ => ∑ i, a i * x i) from by fun_prop).aemeasurable]
  simpa only [pow_two] using! coordinateGaussian_covariance_linear ι a a

/-- A scalar linear combination, bundled to use Gaussian pushforward results. -/
def gaussianLinearFunctional (a : ι → ℝ) : (ι → ℝ) →L[ℝ] ℝ :=
  ∑ i, a i • ContinuousLinearMap.proj i

@[simp] theorem gaussianLinearFunctional_apply (a x : ι → ℝ) :
    gaussianLinearFunctional ι a x = ∑ i, a i * x i := by
  simp [gaussianLinearFunctional]

theorem coordinateGaussian_map_linear (a : ι → ℝ) :
    (coordinateGaussian ι).map (fun x : ι → ℝ => ∑ i, a i * x i) =
      gaussianReal 0 (∑ i, a i ^ 2).toNNReal := by
  simpa only [show (⇑(gaussianLinearFunctional ι a)) =
      (fun x : ι → ℝ => ∑ i, a i * x i) from funext (gaussianLinearFunctional_apply ι a),
    coordinateGaussian_mean_linear,
    coordinateGaussian_variance_linear] using!
    IsGaussian.map_eq_gaussianReal (μ := coordinateGaussian ι) (gaussianLinearFunctional ι a)

/-- An orthogonal family of linear combinations of standard Gaussian coordinates is independent. -/
theorem coordinateGaussian_independent_linear {κ : Type*} [Fintype κ] (A : κ → ι → ℝ)
    (horth : ∀ i j, i ≠ j → ∑ k, A i k * A j k = 0) :
    iIndepFun (fun i (x : ι → ℝ) => ∑ k, A i k * x k) (coordinateGaussian ι) := by
  have hG : HasGaussianLaw (fun x : ι → ℝ => fun i => ∑ k, A i k * x k)
      (coordinateGaussian ι) := by
    simpa only [ContinuousLinearMap.coe_pi', gaussianLinearFunctional_apply, id_eq] using!
      (IsGaussian.hasGaussianLaw_id (μ := coordinateGaussian ι)).map_fun
        (ContinuousLinearMap.pi (fun i => gaussianLinearFunctional ι (A i)))
  exact hG.iIndepFun_of_covariance_eq_zero fun i j hij =>
    (coordinateGaussian_covariance_linear ι (A i) (A j)).trans (horth i j hij)

/-- A matrix with orthonormal rows sends a standard Gaussian to a standard Gaussian. -/
theorem coordinateGaussian_map_orthonormal {κ : Type*} [Fintype κ] (A : κ → ι → ℝ)
    (horth : ∀ i j, i ≠ j → ∑ k, A i k * A j k = 0)
    (hnorm : ∀ i, ∑ k, A i k ^ 2 = 1) :
    (coordinateGaussian ι).map (fun x : ι → ℝ => fun i => ∑ k, A i k * x k) =
      coordinateGaussian κ := by
  refine ((iIndepFun_iff_map_fun_eq_pi_map (fun i =>
    (show Measurable (fun x : ι → ℝ => ∑ k, A i k * x k) from by fun_prop).aemeasurable)).mp
      (coordinateGaussian_independent_linear ι A horth)).trans ?_
  simp only [coordinateGaussian_map_linear, hnorm, Real.toNNReal_one]
  rfl

end ConvexBodyChasing

end
end BundledModule060

/- Component source: ConvexBodyChasing.GaussianNoise -/
section BundledModule061
/-! # Gaussian mixing preserves the standard Gaussian law

Mixing two independent standard Gaussian vectors with coefficients whose
squares sum to one preserves their marginal law.  This is the distributional
ingredient of the Gaussian noise operator.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace ConvexBodyChasing

variable (ι : Type*) [Fintype ι]

theorem coordinateGaussian_rotation (θ : ℝ) :
    MeasurePreserving (ContinuousLinearMap.rotation (E := ι → ℝ) θ)
      ((coordinateGaussian ι).prod (coordinateGaussian ι))
      ((coordinateGaussian ι).prod (coordinateGaussian ι)) :=
  ⟨(ContinuousLinearMap.rotation θ).continuous.measurable,
    IsGaussian.map_rotation_eq_self (coordinateGaussian_integral_id ι) θ⟩

/-- The first component of an orthogonal Gaussian mixing map. -/
def gaussianNoiseMix (t : ℝ) : ((ι → ℝ) × (ι → ℝ)) →L[ℝ] (ι → ℝ) :=
  (ContinuousLinearMap.fst ℝ (ι → ℝ) (ι → ℝ)).comp
    (ContinuousLinearMap.rotation (Real.arccos t))

theorem gaussianNoiseMix_preserving (t : ℝ) :
    MeasurePreserving (gaussianNoiseMix ι t)
      ((coordinateGaussian ι).prod (coordinateGaussian ι)) (coordinateGaussian ι) :=
  measurePreserving_fst.comp (coordinateGaussian_rotation ι (Real.arccos t))

theorem gaussianNoiseMix_apply {t : ℝ} (ht : -1 ≤ t) (ht1 : t ≤ 1)
    (x y : ι → ℝ) :
    gaussianNoiseMix ι t (x, y) = t • x + Real.sqrt (1 - t ^ 2) • y := by
  simp [gaussianNoiseMix, ContinuousLinearMap.rotation_apply, Real.cos_arccos ht ht1,
    Real.sin_arccos]

variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Jensen's inequality for the squared norm of a Bochner expectation. -/
theorem norm_integral_sq_le_integral_norm_sq {f : Ω → E} (hf : Integrable f μ)
    (hsq : Integrable (fun x => ‖f x‖ ^ 2) μ) :
    ‖∫ x, f x ∂μ‖ ^ 2 ≤ ∫ x, ‖f x‖ ^ 2 ∂μ := by
  exact (convexOn_univ_norm.pow (fun _ _ => norm_nonneg _) 2).map_integral_le
    (continuous_norm.pow 2).continuousOn isClosed_univ
    (Filter.Eventually.of_forall (fun _ => Set.mem_univ _)) hf hsq

variable {Ω' : Type*} [MeasurableSpace Ω'] {ν : Measure Ω'} [IsProbabilityMeasure ν]

/-- Averaging one variable is a contraction for the squared Banach-valued `L²` norm. -/
theorem memLp_average_and_integral_norm_sq_le {f : Ω × Ω' → E}
    (hf : MemLp f 2 (μ.prod ν)) :
    MemLp (fun x => ∫ y, f (x, y) ∂ν) 2 μ ∧
      (∫ x, ‖∫ y, f (x, y) ∂ν‖ ^ 2 ∂μ) ≤ ∫ z, ‖f z‖ ^ 2 ∂μ.prod ν := by
  have hfi : Integrable f (μ.prod ν) := hf.integrable (by norm_num)
  have hsq : Integrable (fun z => ‖f z‖ ^ 2) (μ.prod ν) :=
    hf.integrable_norm_pow (by norm_num)
  have hbound : ∀ᵐ x ∂μ, ‖∫ y, f (x, y) ∂ν‖ ^ 2 ≤ ∫ y, ‖f (x, y)‖ ^ 2 ∂ν :=
    hfi.prod_right_ae.mp (hsq.prod_right_ae.mono fun _ hs hi =>
      norm_integral_sq_le_integral_norm_sq hi hs)
  have hmeas := hfi.aestronglyMeasurable.integral_prod_right'
  have hint : Integrable (fun x => ‖∫ y, f (x, y) ∂ν‖ ^ 2) μ :=
    hsq.integral_prod_left.mono' (hmeas.norm.pow 2)
      (hbound.mono fun _ hx => by simpa only [Real.norm_eq_abs, abs_pow, abs_norm] using! hx)
  exact ⟨(memLp_two_iff_integrable_sq_norm hmeas).mpr hint,
    (integral_mono_ae hint hsq.integral_prod_left hbound).trans_eq (integral_prod _ hsq).symm⟩

/-- Gaussian noise averaging, defined for actual Banach-valued functions. -/
def gaussianNoise (t : ℝ) (f : (ι → ℝ) → E) (x : ι → ℝ) : E :=
  ∫ y, f (gaussianNoiseMix ι t (x, y)) ∂coordinateGaussian ι









/-- Gaussian noise preserves `L²` membership and contracts its squared norm. -/
theorem gaussianNoise_memLp_and_integral_norm_sq_le (t : ℝ) {f : (ι → ℝ) → E}
    (hf : MemLp f 2 (coordinateGaussian ι)) :
    MemLp (gaussianNoise ι t f) 2 (coordinateGaussian ι) ∧
      (∫ x, ‖gaussianNoise ι t f x‖ ^ 2 ∂coordinateGaussian ι) ≤
        ∫ x, ‖f x‖ ^ 2 ∂coordinateGaussian ι := by
  have h := memLp_average_and_integral_norm_sq_le
    (hf.comp_measurePreserving (gaussianNoiseMix_preserving ι t))
  exact ⟨h.1, h.2.trans_eq ((gaussianNoiseMix_preserving ι t).hasLaw.integral_comp
    (hf.aestronglyMeasurable.norm.pow 2))⟩

end ConvexBodyChasing

end
end BundledModule061

/- Component source: ConvexBodyChasing.GaussianNoiseLp -/
section BundledModule062
/-! # Gaussian noise as a continuous linear contraction on L²

The operator is defined on equivalence classes of actual measurable functions.
Almost-everywhere congruence and linearity are proved before bundling it.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace ConvexBodyChasing

theorem norm_Lp_two_eq_sqrt_integral {Ω F : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup F] (μ : Measure Ω) (f : Lp F 2 μ) :
    ‖f‖ = Real.sqrt (∫ x, ‖f x‖ ^ 2 ∂μ) := by
  rw [Lp.norm_def, toReal_eLpNorm (Lp.aestronglyMeasurable f)]
  simpa [Real.sqrt_eq_rpow] using! lpNorm_eq_integral_norm_rpow_toReal
    (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num) (Lp.aestronglyMeasurable f)

variable (ι : Type*) [Fintype ι]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem gaussianNoise_congr_ae (t : ℝ) {f g : (ι → ℝ) → E}
    (hfg : f =ᵐ[coordinateGaussian ι] g) :
    gaussianNoise ι t f =ᵐ[coordinateGaussian ι] gaussianNoise ι t g := by
  exact (Measure.ae_ae_of_ae_prod
    ((gaussianNoiseMix_preserving ι t).quasiMeasurePreserving.ae_eq hfg)).mono
    (fun _ h => integral_congr_ae h)

theorem gaussianNoise_add_ae (t : ℝ) {f g : (ι → ℝ) → E}
    (hf : MemLp f 2 (coordinateGaussian ι)) (hg : MemLp g 2 (coordinateGaussian ι)) :
    gaussianNoise ι t (f + g) =ᵐ[coordinateGaussian ι]
      gaussianNoise ι t f + gaussianNoise ι t g := by
  exact (((hf.comp_measurePreserving (gaussianNoiseMix_preserving ι t)).integrable
    (by norm_num)).prod_right_ae.and
    ((hg.comp_measurePreserving (gaussianNoiseMix_preserving ι t)).integrable
      (by norm_num)).prod_right_ae).mono (fun _ h => integral_add h.1 h.2)

theorem gaussianNoise_smul (t c : ℝ) (f : (ι → ℝ) → E) :
    gaussianNoise ι t (c • f) = c • gaussianNoise ι t f := by
  exact funext (fun _ => integral_smul c _)

variable [CompleteSpace E]

/-- Gaussian noise on equivalence classes in Banach-valued L². -/
def gaussianNoiseL2 (t : ℝ) (f : Lp E 2 (coordinateGaussian ι)) :
    Lp E 2 (coordinateGaussian ι) :=
  (gaussianNoise_memLp_and_integral_norm_sq_le ι t (Lp.memLp f)).1.toLp
    (gaussianNoise ι t f)

theorem gaussianNoiseL2_ae (t : ℝ) (f : Lp E 2 (coordinateGaussian ι)) :
    gaussianNoiseL2 ι t f =ᵐ[coordinateGaussian ι] gaussianNoise ι t f :=
  (gaussianNoise_memLp_and_integral_norm_sq_le ι t (Lp.memLp f)).1.coeFn_toLp

theorem gaussianNoiseL2_add (t : ℝ) (f g : Lp E 2 (coordinateGaussian ι)) :
    gaussianNoiseL2 ι t (f + g) = gaussianNoiseL2 ι t f + gaussianNoiseL2 ι t g := by
  apply Lp.ext
  exact (gaussianNoiseL2_ae ι t (f + g)).trans
    ((gaussianNoise_congr_ae ι t (Lp.coeFn_add f g)).trans
      ((gaussianNoise_add_ae ι t (Lp.memLp f) (Lp.memLp g)).trans
        (((gaussianNoiseL2_ae ι t f).add (gaussianNoiseL2_ae ι t g)).symm.trans
          (Lp.coeFn_add _ _).symm)))

theorem gaussianNoiseL2_smul (t c : ℝ) (f : Lp E 2 (coordinateGaussian ι)) :
    gaussianNoiseL2 ι t (c • f) = c • gaussianNoiseL2 ι t f := by
  apply Lp.ext
  exact (gaussianNoiseL2_ae ι t (c • f)).trans
    ((gaussianNoise_congr_ae ι t (Lp.coeFn_smul c f)).trans
      (Filter.EventuallyEq.trans (Filter.Eventually.of_forall (congrFun (gaussianNoise_smul ι t c f)))
        (((gaussianNoiseL2_ae ι t f).const_smul c).symm.trans (Lp.coeFn_smul c _).symm)))

theorem norm_gaussianNoiseL2_le (t : ℝ) (f : Lp E 2 (coordinateGaussian ι)) :
    ‖gaussianNoiseL2 ι t f‖ ≤ ‖f‖ := by
  rw [norm_Lp_two_eq_sqrt_integral, norm_Lp_two_eq_sqrt_integral]
  exact Real.sqrt_le_sqrt
    ((integral_congr_ae ((gaussianNoiseL2_ae ι t f).mono
      (fun _ hx => congrArg (fun v : E => ‖v‖ ^ 2) hx))).trans_le
      (gaussianNoise_memLp_and_integral_norm_sq_le ι t (Lp.memLp f)).2)

def gaussianNoiseLinear (t : ℝ) :
    Lp E 2 (coordinateGaussian ι) →ₗ[ℝ] Lp E 2 (coordinateGaussian ι) where
  toFun := gaussianNoiseL2 ι t
  map_add' := gaussianNoiseL2_add ι t
  map_smul' := gaussianNoiseL2_smul ι t

/-- The Gaussian noise operator as a continuous linear contraction. -/
def gaussianNoiseCLM (t : ℝ) :
    Lp E 2 (coordinateGaussian ι) →L[ℝ] Lp E 2 (coordinateGaussian ι) :=
  (gaussianNoiseLinear ι t).mkContinuous 1
    (fun f => by simpa only [one_mul] using! norm_gaussianNoiseL2_le ι t f)





end ConvexBodyChasing

end
end BundledModule062

/- Component source: ConvexBodyChasing.GaussianNoiseSymmetry -/
section BundledModule063
/-! # Symmetry of Gaussian noise

A measure-preserving involution exchanges a Gaussian input and its noisy
output.  This supplies the symmetry identity for the L² noise operator.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace ConvexBodyChasing

variable (ι : Type*) [Fintype ι]

theorem coordinateGaussian_neg_preserving :
    MeasurePreserving (fun x : ι → ℝ => -x) (coordinateGaussian ι) (coordinateGaussian ι) := by
  exact measurePreserving_pi (fun _ : ι => gaussianReal 0 1) (fun _ : ι => gaussianReal 0 1)
    (fun _ => ⟨measurable_neg, by simpa using! (gaussianReal_map_neg (μ := 0) (v := 1))⟩)

/-- A reflection of the pair that exchanges the input and its noisy output. -/
def gaussianNoiseReflection (t : ℝ) (z : (ι → ℝ) × (ι → ℝ)) :
    (ι → ℝ) × (ι → ℝ) :=
  let w := ContinuousLinearMap.rotation (Real.arccos t) z
  (w.1, -w.2)

theorem gaussianNoiseReflection_preserving (t : ℝ) :
    MeasurePreserving (gaussianNoiseReflection ι t)
      ((coordinateGaussian ι).prod (coordinateGaussian ι))
      ((coordinateGaussian ι).prod (coordinateGaussian ι)) :=
  ((MeasurePreserving.id (coordinateGaussian ι)).prod (coordinateGaussian_neg_preserving ι)).comp
    (coordinateGaussian_rotation ι (Real.arccos t))



@[simp] theorem gaussianNoiseReflection_fst (t : ℝ) (z : (ι → ℝ) × (ι → ℝ)) :
    (gaussianNoiseReflection ι t z).1 = gaussianNoiseMix ι t z := rfl

@[simp] theorem gaussianNoiseMix_reflection (t : ℝ) (z : (ι → ℝ) × (ι → ℝ)) :
    gaussianNoiseMix ι t (gaussianNoiseReflection ι t z) = z.1 := by
  ext i
  simp only [gaussianNoiseMix, gaussianNoiseReflection, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.rotation_apply, Pi.add_apply,
    Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  linear_combination z.1 i * Real.cos_sq_add_sin_sq (Real.arccos t)

/-- The joint law of the input and its noisy output is exchangeable. -/
theorem gaussianNoiseMix_integral_exchange (t : ℝ) (Φ : (ι → ℝ) → (ι → ℝ) → ℝ)
    (hΦ : AEStronglyMeasurable (fun z => Φ z.1 (gaussianNoiseMix ι t z))
      ((coordinateGaussian ι).prod (coordinateGaussian ι))) :
    (∫ z, Φ (gaussianNoiseMix ι t z) z.1 ∂(coordinateGaussian ι).prod (coordinateGaussian ι)) =
      ∫ z, Φ z.1 (gaussianNoiseMix ι t z) ∂(coordinateGaussian ι).prod (coordinateGaussian ι) := by
  simpa only [Function.comp_apply, gaussianNoiseReflection_fst, gaussianNoiseMix_reflection] using!
    (gaussianNoiseReflection_preserving ι t).hasLaw.integral_comp hΦ

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem integrable_real_inner_of_memLp_two {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f g : Ω → H} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun x => inner ℝ (f x) (g x)) μ := by
  exact (hf.norm.integrable_mul hg.norm).mono' (hf.aestronglyMeasurable.inner hg.aestronglyMeasurable)
    (Filter.Eventually.of_forall (fun x => norm_inner_le_norm (f x) (g x)))

variable [CompleteSpace H]

theorem gaussianNoise_inner_eq_integral_pair (t : ℝ) {f g : (ι → ℝ) → H}
    (hf : MemLp f 2 (coordinateGaussian ι)) (hg : MemLp g 2 (coordinateGaussian ι)) :
    (∫ x, inner ℝ (f x) (gaussianNoise ι t g x) ∂coordinateGaussian ι) =
      ∫ z, inner ℝ (f z.1) (g (gaussianNoiseMix ι t z))
        ∂(coordinateGaussian ι).prod (coordinateGaussian ι) := by
  have hint := integrable_real_inner_of_memLp_two
    (hf.comp_measurePreserving (measurePreserving_fst (ν := coordinateGaussian ι)))
    (hg.comp_measurePreserving (gaussianNoiseMix_preserving ι t))
  refine Eq.trans ?_ (integral_prod _ hint).symm
  exact integral_congr_ae
    (((hg.comp_measurePreserving (gaussianNoiseMix_preserving ι t)).integrable
      (by norm_num)).prod_right_ae.mono (fun x hx => (integral_inner hx (f x)).symm))

theorem gaussianNoise_inner_symmetry (t : ℝ) {f g : (ι → ℝ) → H}
    (hf : MemLp f 2 (coordinateGaussian ι)) (hg : MemLp g 2 (coordinateGaussian ι)) :
    (∫ x, inner ℝ (f x) (gaussianNoise ι t g x) ∂coordinateGaussian ι) =
      ∫ x, inner ℝ (gaussianNoise ι t f x) (g x) ∂coordinateGaussian ι := by
  have hex := gaussianNoiseMix_integral_exchange ι t (fun x y => inner ℝ (g x) (f y))
    ((hg.comp_measurePreserving (measurePreserving_fst (ν := coordinateGaussian ι))).1.inner
      (hf.comp_measurePreserving (gaussianNoiseMix_preserving ι t)).1)
  calc
    _ = ∫ z, inner ℝ (f z.1) (g (gaussianNoiseMix ι t z))
        ∂(coordinateGaussian ι).prod (coordinateGaussian ι) :=
      gaussianNoise_inner_eq_integral_pair ι t hf hg
    _ = ∫ z, inner ℝ (g z.1) (f (gaussianNoiseMix ι t z))
        ∂(coordinateGaussian ι).prod (coordinateGaussian ι) := by
      simpa only [real_inner_comm] using! hex
    _ = ∫ x, inner ℝ (g x) (gaussianNoise ι t f x) ∂coordinateGaussian ι :=
      (gaussianNoise_inner_eq_integral_pair ι t hg hf).symm
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall (fun _ => real_inner_comm _ _))

/-- Gaussian noise is symmetric as a continuous linear operator on Hilbert-valued L². -/
theorem gaussianNoiseCLM_isSymmetric (t : ℝ) :
    (gaussianNoiseCLM (E := H) ι t).toLinearMap.IsSymmetric := by
  intro f g
  calc
    _ = ∫ x, inner ℝ (gaussianNoise ι t f x) (g x) ∂coordinateGaussian ι :=
      integral_congr_ae ((gaussianNoiseL2_ae ι t f).mono
        (fun x hx => congrArg (fun v => inner ℝ v (g x)) hx))
    _ = ∫ x, inner ℝ (f x) (gaussianNoise ι t g x) ∂coordinateGaussian ι :=
      (gaussianNoise_inner_symmetry ι t (Lp.memLp f) (Lp.memLp g)).symm
    _ = _ := integral_congr_ae ((gaussianNoiseL2_ae ι t g).symm.mono
      (fun x hx => congrArg (inner ℝ (f x)) hx))

end ConvexBodyChasing

end
end BundledModule063

/- Component source: ConvexBodyChasing.GaussianPolynomials -/
section BundledModule064
/-! # Polynomial subspaces of Gaussian L²

Polynomial evaluations have every finite Gaussian moment.  They embed into
L², and the subspaces of bounded total degree are finite dimensional.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace ConvexBodyChasing

variable (ι : Type*) [Fintype ι]

theorem coordinateGaussian_memLp_polynomial (P : MvPolynomial ι ℝ)
    (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (fun x : ι → ℝ => MvPolynomial.eval x P) p (coordinateGaussian ι) := by
  induction P using MvPolynomial.induction_on generalizing p with
  | C a => simpa only [MvPolynomial.eval_C] using! memLp_const a
  | add P Q hP hQ => simpa only [MvPolynomial.eval_add] using! (hP p hp).add (hQ p hp)
  | mul_X P i hP =>
    letI : ENNReal.HolderTriple (2 * p) (2 * p) p := ⟨by
      rw [ENNReal.mul_inv (Or.inl two_ne_zero) (Or.inl ENNReal.ofNat_ne_top),
        ← add_mul, ENNReal.inv_two_add_inv_two, one_mul]⟩
    simpa only [MvPolynomial.eval_mul, MvPolynomial.eval_X] using!
      ((IsGaussian.memLp_id (coordinateGaussian ι) (2 * p)
        (ENNReal.mul_ne_top ENNReal.ofNat_ne_top hp)).eval i).mul'
          (hP (2 * p) (ENNReal.mul_ne_top ENNReal.ofNat_ne_top hp))

def gaussianPolynomialL2 (P : MvPolynomial ι ℝ) : Lp ℝ 2 (coordinateGaussian ι) :=
  (coordinateGaussian_memLp_polynomial ι P 2 (by norm_num)).toLp
    (fun x : ι → ℝ => MvPolynomial.eval x P)

theorem gaussianPolynomialL2_ae (P : MvPolynomial ι ℝ) :
    gaussianPolynomialL2 ι P =ᵐ[coordinateGaussian ι] fun x : ι → ℝ => MvPolynomial.eval x P :=
  (coordinateGaussian_memLp_polynomial ι P 2 (by norm_num)).coeFn_toLp

theorem gaussianPolynomialL2_add (P Q : MvPolynomial ι ℝ) :
    gaussianPolynomialL2 ι (P + Q) = gaussianPolynomialL2 ι P + gaussianPolynomialL2 ι Q := by
  apply Lp.ext
  filter_upwards [gaussianPolynomialL2_ae ι (P + Q), gaussianPolynomialL2_ae ι P,
    gaussianPolynomialL2_ae ι Q, Lp.coeFn_add (gaussianPolynomialL2 ι P) (gaussianPolynomialL2 ι Q)]
    with x hsum hP hQ hadd
  simp only [hsum, hadd, Pi.add_apply, hP, hQ, MvPolynomial.eval_add]

theorem gaussianPolynomialL2_smul (c : ℝ) (P : MvPolynomial ι ℝ) :
    gaussianPolynomialL2 ι (c • P) = c • gaussianPolynomialL2 ι P := by
  apply Lp.ext
  filter_upwards [gaussianPolynomialL2_ae ι (c • P), gaussianPolynomialL2_ae ι P,
    Lp.coeFn_smul c (gaussianPolynomialL2 ι P)] with x hsmul hP hcoe
  rw [hsmul, hcoe, Pi.smul_apply, hP, MvPolynomial.smul_eval, smul_eq_mul]

def gaussianPolynomialEmbedding : MvPolynomial ι ℝ →ₗ[ℝ] Lp ℝ 2 (coordinateGaussian ι) where
  toFun := gaussianPolynomialL2 ι
  map_add' := gaussianPolynomialL2_add ι
  map_smul' := gaussianPolynomialL2_smul ι



/-- The Gaussian L² subspace of polynomials of total degree at most `d`. -/
def gaussianPolynomialSpace (d : ℕ) : Submodule ℝ (Lp ℝ 2 (coordinateGaussian ι)) :=
  (MvPolynomial.restrictTotalDegree ι ℝ d).map (gaussianPolynomialEmbedding ι)

theorem mem_gaussianPolynomialSpace_iff (d : ℕ) (f : Lp ℝ 2 (coordinateGaussian ι)) :
    f ∈ gaussianPolynomialSpace ι d ↔
      ∃ P : MvPolynomial ι ℝ, P.totalDegree ≤ d ∧ gaussianPolynomialL2 ι P = f := by
  simp only [gaussianPolynomialSpace, Submodule.mem_map, MvPolynomial.mem_restrictTotalDegree,
    gaussianPolynomialEmbedding, LinearMap.coe_mk, AddHom.coe_mk]

theorem gaussianPolynomialSpace_mono : Monotone (gaussianPolynomialSpace ι) := by
  intro d e hde
  exact Submodule.map_mono (fun P hP => (MvPolynomial.mem_restrictTotalDegree ι e P).mpr
    (((MvPolynomial.mem_restrictTotalDegree ι d P).mp hP).trans hde))

instance gaussianPolynomialSpace_finiteDimensional (d : ℕ) :
    FiniteDimensional ℝ (gaussianPolynomialSpace ι d) := by
  unfold gaussianPolynomialSpace
  infer_instance



end ConvexBodyChasing

end
end BundledModule064

/- Component source: ConvexBodyChasing.PolynomialDegree -/
section BundledModule065
/-! # Strict polynomial degree filtration

The strict filtration includes the zero space at degree zero.  This makes
the lower-degree error of affine substitution uniform even for constants.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped Pointwise
namespace ConvexBodyChasing

variable (ι S : Type*) [CommRing S]

def polynomialDegreeLT (d : ℕ) : Submodule S (MvPolynomial ι S) :=
  MvPolynomial.restrictSupport S {m | m.degree < d}



theorem polynomialDegreeLT_succ (d : ℕ) :
    polynomialDegreeLT ι S (d + 1) = MvPolynomial.restrictTotalDegree ι S d := by
  exact congrArg (MvPolynomial.restrictSupport S) (Set.ext fun _ => Nat.lt_succ_iff)

theorem polynomialDegreeLT_zero : polynomialDegreeLT ι S 0 = ⊥ := by
  ext P
  simp [polynomialDegreeLT, MvPolynomial.mem_restrictSupport_iff]

theorem polynomialDegreeLE_le_lt {m n : ℕ} (h : m < n) :
    MvPolynomial.restrictTotalDegree ι S m ≤ polynomialDegreeLT ι S n := by
  exact MvPolynomial.restrictSupport_mono S (fun _ hm => Nat.lt_of_le_of_lt hm h)

theorem polynomial_restrictSupport_map {T : Type*} [CommRing T] (f : S →+* T)
    {s : Set (ι →₀ ℕ)} {P : MvPolynomial ι S}
    (hP : P ∈ MvPolynomial.restrictSupport S s) :
    MvPolynomial.map f P ∈ MvPolynomial.restrictSupport T s := by
  exact (MvPolynomial.mem_restrictSupport_iff T).mpr (fun _ hm =>
    (MvPolynomial.mem_restrictSupport_iff S).mp hP (MvPolynomial.support_map_subset f P hm))

theorem polynomialDegreeLE_map {T : Type*} [CommRing T] (f : S →+* T)
    {d : ℕ} {P : MvPolynomial ι S}
    (hP : P ∈ MvPolynomial.restrictTotalDegree ι S d) :
    MvPolynomial.map f P ∈ MvPolynomial.restrictTotalDegree ι T d :=
  polynomial_restrictSupport_map ι S f hP

theorem polynomialDegreeLT_mul_le {m n : ℕ} {A B : MvPolynomial ι S}
    (hA : A ∈ polynomialDegreeLT ι S m)
    (hB : B ∈ MvPolynomial.restrictTotalDegree ι S n) :
    A * B ∈ polynomialDegreeLT ι S (m + n) := by
  have hp := Submodule.mul_mem_mul hA hB
  rw [polynomialDegreeLT, MvPolynomial.restrictTotalDegree,
    ← MvPolynomial.restrictSupport_add] at hp
  refine MvPolynomial.restrictSupport_mono S ?_ hp
  rintro _ ⟨a, ha, b, hb, rfl⟩
  simpa only [Set.mem_setOf_eq, map_add] using! Nat.add_lt_add_of_lt_of_le ha hb

theorem polynomialDegreeLE_mul_lt {m n : ℕ} {A B : MvPolynomial ι S}
    (hA : A ∈ MvPolynomial.restrictTotalDegree ι S m)
    (hB : B ∈ polynomialDegreeLT ι S n) :
    A * B ∈ polynomialDegreeLT ι S (m + n) := by
  simpa only [mul_comm, Nat.add_comm] using! polynomialDegreeLT_mul_le ι S hB hA

theorem polynomialDegreeLE_mul_le {m n : ℕ} {A B : MvPolynomial ι S}
    (hA : A ∈ MvPolynomial.restrictTotalDegree ι S m)
    (hB : B ∈ MvPolynomial.restrictTotalDegree ι S n) :
    A * B ∈ MvPolynomial.restrictTotalDegree ι S (m + n) := by
  exact (MvPolynomial.mem_restrictTotalDegree ι (m + n) _).mpr
    ((MvPolynomial.totalDegree_mul A B).trans (Nat.add_le_add
      ((MvPolynomial.mem_restrictTotalDegree ι m A).mp hA)
      ((MvPolynomial.mem_restrictTotalDegree ι n B).mp hB)))

theorem polynomial_product_error {m n : ℕ} {A B a b : MvPolynomial ι S}
    (hB : B ∈ MvPolynomial.restrictTotalDegree ι S n)
    (ha : a ∈ MvPolynomial.restrictTotalDegree ι S m)
    (hAa : A - a ∈ polynomialDegreeLT ι S m)
    (hBb : B - b ∈ polynomialDegreeLT ι S n) :
    A * B - a * b ∈ polynomialDegreeLT ι S (m + n) := by
  have heq : A * B - a * b = (A - a) * B + a * (B - b) := by ring
  exact heq.symm ▸ (polynomialDegreeLT ι S (m + n)).add_mem
    (polynomialDegreeLT_mul_le ι S hAa hB) (polynomialDegreeLE_mul_lt ι S ha hBb)

/-- Substitute the same scalar multiple of each variable, plus an arbitrary translation. -/
def affinePolynomialSubstitution (t : S) (y : ι → S) :
    MvPolynomial ι S →ₐ[S] MvPolynomial ι S :=
  MvPolynomial.aeval (fun i => t • MvPolynomial.X i + MvPolynomial.C (y i))



@[simp] theorem affinePolynomialSubstitution_X (t : S) (y : ι → S) (i : ι) :
    affinePolynomialSubstitution ι S t y (MvPolynomial.X i) =
      t • MvPolynomial.X i + MvPolynomial.C (y i) := by
  simp [affinePolynomialSubstitution]

theorem affinePolynomialSubstitution_X_degree [Nontrivial S] (t : S) (y : ι → S) (i : ι) :
    affinePolynomialSubstitution ι S t y (MvPolynomial.X i) ∈
      MvPolynomial.restrictTotalDegree ι S 1 := by
  apply (MvPolynomial.mem_restrictTotalDegree ι 1 _).mpr
  rw [affinePolynomialSubstitution_X]
  exact (MvPolynomial.totalDegree_add _ _).trans (max_le
    ((MvPolynomial.totalDegree_smul_le t _).trans_eq (MvPolynomial.totalDegree_X i))
    (by simp))

theorem affinePolynomialSubstitution_X_error (t : S) (y : ι → S) (i : ι) :
    affinePolynomialSubstitution ι S t y (MvPolynomial.X i) - t • MvPolynomial.X i ∈
      polynomialDegreeLT ι S 1 := by
  simp [affinePolynomialSubstitution_X, polynomialDegreeLT_succ,
    MvPolynomial.mem_restrictTotalDegree]

theorem affinePolynomialSubstitution_eval₂ {T : Type*} [CommRing T]
    (f : S →+* T) (x : ι → T) (t : S) (y : ι → S) (P : MvPolynomial ι S) :
    MvPolynomial.eval₂ f x (affinePolynomialSubstitution ι S t y P) =
      MvPolynomial.eval₂ f (fun i => f t * x i + f (y i)) P := by
  rw [affinePolynomialSubstitution, MvPolynomial.aeval_def,
    MvPolynomial.algebraMap_eq, ← MvPolynomial.eval₂_assoc]
  simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.eval₂_add,
    MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C, MvPolynomial.eval₂_X]

variable [IsDomain S]

theorem affinePolynomialSubstitution_monomial (t : S) (y : ι → S)
    (s : ι →₀ ℕ) (c : S) :
    let P := MvPolynomial.monomial s c
    affinePolynomialSubstitution ι S t y P ∈
        MvPolynomial.restrictTotalDegree ι S P.totalDegree ∧
      affinePolynomialSubstitution ι S t y P - t ^ P.totalDegree • P ∈
        polynomialDegreeLT ι S P.totalDegree := by
  apply MvPolynomial.induction_on_monomial
    (motive := fun P => affinePolynomialSubstitution ι S t y P ∈
        MvPolynomial.restrictTotalDegree ι S P.totalDegree ∧
      affinePolynomialSubstitution ι S t y P - t ^ P.totalDegree • P ∈
        polynomialDegreeLT ι S P.totalDegree)
  case mul_X =>
    intro P i hP
    by_cases hzero : P = 0
    · simp [hzero]
    rw [MvPolynomial.totalDegree_mul_of_isDomain hzero (MvPolynomial.X_ne_zero i),
      MvPolynomial.totalDegree_X, map_mul]
    refine ⟨polynomialDegreeLE_mul_le ι S hP.1
      (affinePolynomialSubstitution_X_degree ι S t y i), ?_⟩
    simpa only [smul_mul_smul_comm, ← pow_succ] using!
      polynomial_product_error ι S (affinePolynomialSubstitution_X_degree ι S t y i)
        ((MvPolynomial.restrictTotalDegree ι S P.totalDegree).smul_mem (t ^ P.totalDegree)
          ((MvPolynomial.mem_restrictTotalDegree ι _ P).mpr le_rfl))
        hP.2 (affinePolynomialSubstitution_X_error ι S t y i)
  case C => simp [MvPolynomial.mem_restrictTotalDegree]

theorem affinePolynomialSubstitution_degree (t : S) (y : ι → S) {d : ℕ}
    {P : MvPolynomial ι S} (hP : P ∈ MvPolynomial.restrictTotalDegree ι S d) :
    affinePolynomialSubstitution ι S t y P ∈ MvPolynomial.restrictTotalDegree ι S d := by
  suffices h : MvPolynomial.restrictTotalDegree ι S d ≤
      (MvPolynomial.restrictTotalDegree ι S d).comap
        (affinePolynomialSubstitution ι S t y).toLinearMap from h hP
  conv_lhs => rw [MvPolynomial.restrictTotalDegree, MvPolynomial.restrictSupport_eq_span]
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨s, hs, rfl⟩
  exact (MvPolynomial.mem_restrictTotalDegree ι d _).mpr
    (((MvPolynomial.mem_restrictTotalDegree ι _ _).mp
      (affinePolynomialSubstitution_monomial ι S t y s 1).1).trans
        (by simpa only [MvPolynomial.totalDegree_monomial s one_ne_zero] using! hs))

/-- Affine substitution acts on the quotient of degree `≤ d` by degree `< d`
as multiplication by `t ^ d`. -/
theorem affinePolynomialSubstitution_error (t : S) (y : ι → S) {d : ℕ}
    {P : MvPolynomial ι S} (hP : P ∈ MvPolynomial.restrictTotalDegree ι S d) :
    affinePolynomialSubstitution ι S t y P - t ^ d • P ∈ polynomialDegreeLT ι S d := by
  suffices h : MvPolynomial.restrictTotalDegree ι S d ≤
      (polynomialDegreeLT ι S d).comap
        ((affinePolynomialSubstitution ι S t y).toLinearMap -
          t ^ d • LinearMap.id) from h hP
  conv_lhs => rw [MvPolynomial.restrictTotalDegree, MvPolynomial.restrictSupport_eq_span]
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨s, hs, rfl⟩
  change affinePolynomialSubstitution ι S t y (MvPolynomial.monomial s 1) -
    t ^ d • MvPolynomial.monomial s 1 ∈ polynomialDegreeLT ι S d
  have he : (MvPolynomial.monomial s (1 : S)).totalDegree ≤ d := by
    simpa only [MvPolynomial.totalDegree_monomial s one_ne_zero] using! hs
  rcases he.lt_or_eq with hlt | rfl
  · exact polynomialDegreeLE_le_lt ι S hlt
      ((MvPolynomial.restrictTotalDegree ι S _).sub_mem
        (affinePolynomialSubstitution_monomial ι S t y s 1).1
        ((MvPolynomial.restrictTotalDegree ι S _).smul_mem (t ^ d)
          ((MvPolynomial.mem_restrictTotalDegree ι _ _).mpr le_rfl)))
  · exact (affinePolynomialSubstitution_monomial ι S t y s 1).2

end ConvexBodyChasing

end
end BundledModule065

/- Component source: ConvexBodyChasing.PolynomialExpectation -/
section BundledModule066
/-! # Gaussian expectation of polynomial coefficients

Integrating the coefficients of a polynomial preserves its degree bound.
This realizes averaging over a second set of Gaussian variables by an
actual polynomial, without assuming polynomial invariance of the noise operator.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open MeasureTheory ProbabilityTheory
namespace ConvexBodyChasing

variable (ι : Type*) [Fintype ι]

def gaussianPolynomialExpectation : MvPolynomial ι ℝ →ₗ[ℝ] ℝ where
  toFun P := ∫ y, MvPolynomial.eval y P ∂coordinateGaussian ι
  map_add' P Q := by
    simpa only [MvPolynomial.eval_add] using! integral_add
      ((coordinateGaussian_memLp_polynomial ι P 1 (by norm_num)).integrable le_rfl)
      ((coordinateGaussian_memLp_polynomial ι Q 1 (by norm_num)).integrable le_rfl)
  map_smul' c P := by simp [MvPolynomial.smul_eval, integral_const_mul]

@[simp] theorem gaussianPolynomialExpectation_C (c : ℝ) :
    gaussianPolynomialExpectation ι (MvPolynomial.C c) = c := by
  simp [gaussianPolynomialExpectation]

variable (κ : Type*)

def gaussianCoefficientExpectation :
    MvPolynomial κ (MvPolynomial ι ℝ) →ₗ[ℝ] MvPolynomial κ ℝ :=
  (AddMonoidAlgebra.coeffLinearEquiv ℝ).symm.toLinearMap ∘ₗ
    Finsupp.mapRange.linearMap (gaussianPolynomialExpectation ι) ∘ₗ
      (AddMonoidAlgebra.coeffLinearEquiv ℝ).toLinearMap

@[simp] theorem gaussianCoefficientExpectation_coeff
    (P : MvPolynomial κ (MvPolynomial ι ℝ)) (m : κ →₀ ℕ) :
    MvPolynomial.coeff m (gaussianCoefficientExpectation ι κ P) =
      gaussianPolynomialExpectation ι (MvPolynomial.coeff m P) := by
  rfl

theorem gaussianCoefficientExpectation_support (P : MvPolynomial κ (MvPolynomial ι ℝ)) :
    (gaussianCoefficientExpectation ι κ P).support ⊆ P.support := by
  exact Finsupp.support_mapRange (hf := map_zero (gaussianPolynomialExpectation ι))

@[simp] theorem gaussianCoefficientExpectation_monomial (m : κ →₀ ℕ)
    (P : MvPolynomial ι ℝ) :
    gaussianCoefficientExpectation ι κ (MvPolynomial.monomial m P) =
      MvPolynomial.monomial m (gaussianPolynomialExpectation ι P) := by
  apply AddMonoidAlgebra.coeff_injective
  exact Finsupp.mapRange_single (hf := map_zero (gaussianPolynomialExpectation ι))

theorem gaussianCoefficientExpectation_restrictSupport {s : Set (κ →₀ ℕ)}
    {P : MvPolynomial κ (MvPolynomial ι ℝ)}
    (hP : P ∈ MvPolynomial.restrictSupport (MvPolynomial ι ℝ) s) :
    gaussianCoefficientExpectation ι κ P ∈ MvPolynomial.restrictSupport ℝ s := by
  exact (MvPolynomial.mem_restrictSupport_iff ℝ).mpr (fun _ hm =>
    (MvPolynomial.mem_restrictSupport_iff (MvPolynomial ι ℝ)).mp hP
      (gaussianCoefficientExpectation_support ι κ P hm))

theorem gaussianCoefficientExpectation_degree {d : ℕ}
    {P : MvPolynomial κ (MvPolynomial ι ℝ)}
    (hP : P ∈ MvPolynomial.restrictTotalDegree κ (MvPolynomial ι ℝ) d) :
    gaussianCoefficientExpectation ι κ P ∈ MvPolynomial.restrictTotalDegree κ ℝ d :=
  gaussianCoefficientExpectation_restrictSupport ι κ hP

theorem gaussianCoefficientExpectation_degreeLT {d : ℕ}
    {P : MvPolynomial κ (MvPolynomial ι ℝ)}
    (hP : P ∈ polynomialDegreeLT κ (MvPolynomial ι ℝ) d) :
    gaussianCoefficientExpectation ι κ P ∈ polynomialDegreeLT κ ℝ d :=
  gaussianCoefficientExpectation_restrictSupport ι κ hP

theorem coordinateGaussian_integrable_eval₂ (P : MvPolynomial κ (MvPolynomial ι ℝ))
    (x : κ → ℝ) :
    Integrable (fun y => MvPolynomial.eval₂ (MvPolynomial.eval y) x P)
      (coordinateGaussian ι) := by
  induction P using MvPolynomial.induction_on' with
  | add P Q hP hQ =>
    simpa only [MvPolynomial.eval₂_add] using! hP.add hQ
  | monomial m P =>
    simpa only [MvPolynomial.eval₂_monomial] using!
      ((coordinateGaussian_memLp_polynomial ι P 1 (by norm_num)).integrable le_rfl).mul_const
        (m.prod fun i e => x i ^ e)

theorem gaussianCoefficientExpectation_eval (P : MvPolynomial κ (MvPolynomial ι ℝ))
    (x : κ → ℝ) :
    MvPolynomial.eval x (gaussianCoefficientExpectation ι κ P) =
      ∫ y, MvPolynomial.eval₂ (MvPolynomial.eval y) x P ∂coordinateGaussian ι := by
  induction P using MvPolynomial.induction_on' with
  | add P Q hP hQ =>
    simp only [map_add, MvPolynomial.eval₂_add, hP, hQ,
      integral_add (coordinateGaussian_integrable_eval₂ ι κ P x)
        (coordinateGaussian_integrable_eval₂ ι κ Q x)]
  | monomial m P =>
    simp [gaussianPolynomialExpectation, MvPolynomial.eval₂_monomial,
      MvPolynomial.eval_monomial, integral_mul_const]

@[simp] theorem gaussianCoefficientExpectation_map_C (P : MvPolynomial κ ℝ) :
    gaussianCoefficientExpectation ι κ (MvPolynomial.map MvPolynomial.C P) = P := by
  ext m
  simp only [gaussianCoefficientExpectation_coeff, MvPolynomial.coeff_map,
    gaussianPolynomialExpectation_C]

end ConvexBodyChasing

end
end BundledModule066

/- Component source: ConvexBodyChasing.GaussianPolynomialNoise -/
section BundledModule067
/-! # Gaussian noise on polynomial degree spaces

Polynomial coefficients in a second variable set encode affine mixing.
Their Gaussian expectations realize the noise operator and identify its
leading-degree action.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open MeasureTheory ProbabilityTheory
namespace ConvexBodyChasing

variable (ι : Type*) [Fintype ι]

/-- The polynomial `P(t x + s y)`, with the `y` variables in the coefficient ring. -/
def gaussianMixedPolynomial (t s : ℝ) (P : MvPolynomial ι ℝ) :
    MvPolynomial ι (MvPolynomial ι ℝ) :=
  affinePolynomialSubstitution ι (MvPolynomial ι ℝ) (MvPolynomial.C t)
    (fun i => s • MvPolynomial.X i) (MvPolynomial.map MvPolynomial.C P)

/-- Average the second set of variables in an affine polynomial mixture. -/
def gaussianAveragePolynomial (t s : ℝ) (P : MvPolynomial ι ℝ) : MvPolynomial ι ℝ :=
  gaussianCoefficientExpectation ι ι (gaussianMixedPolynomial ι t s P)

omit [Fintype ι] in
theorem gaussianMixedPolynomial_eval (t s : ℝ) (P : MvPolynomial ι ℝ) (x y : ι → ℝ) :
    MvPolynomial.eval₂ (MvPolynomial.eval y) x (gaussianMixedPolynomial ι t s P) =
      MvPolynomial.eval (t • x + s • y) P := by
  rw [gaussianMixedPolynomial, affinePolynomialSubstitution_eval₂, MvPolynomial.eval₂_map]
  have hC : (MvPolynomial.eval y).comp (MvPolynomial.C : ℝ →+* MvPolynomial ι ℝ) =
      RingHom.id ℝ := RingHom.ext (fun c => MvPolynomial.eval_C c)
  simp only [hC, MvPolynomial.eval_C, MvPolynomial.smul_eval, MvPolynomial.eval_X,
    MvPolynomial.eval₂_id]
  rfl

theorem gaussianAveragePolynomial_eval (t s : ℝ) (P : MvPolynomial ι ℝ) (x : ι → ℝ) :
    MvPolynomial.eval x (gaussianAveragePolynomial ι t s P) =
      ∫ y, MvPolynomial.eval (t • x + s • y) P ∂coordinateGaussian ι := by
  simp only [gaussianAveragePolynomial, gaussianCoefficientExpectation_eval,
    gaussianMixedPolynomial_eval]

theorem gaussianAveragePolynomial_eq_noise {t : ℝ} (ht : -1 ≤ t) (ht1 : t ≤ 1)
    (P : MvPolynomial ι ℝ) (x : ι → ℝ) :
    MvPolynomial.eval x (gaussianAveragePolynomial ι t (Real.sqrt (1 - t ^ 2)) P) =
      gaussianNoise ι t (fun z => MvPolynomial.eval z P) x := by
  simp only [gaussianAveragePolynomial_eval, gaussianNoise, gaussianNoiseMix_apply ι ht ht1]

omit [Fintype ι] in
theorem gaussianMixedPolynomial_degree (t s : ℝ) {d : ℕ} {P : MvPolynomial ι ℝ}
    (hP : P ∈ MvPolynomial.restrictTotalDegree ι ℝ d) :
    gaussianMixedPolynomial ι t s P ∈
      MvPolynomial.restrictTotalDegree ι (MvPolynomial ι ℝ) d :=
  affinePolynomialSubstitution_degree ι (MvPolynomial ι ℝ) _ _
    (polynomialDegreeLE_map ι ℝ MvPolynomial.C hP)

theorem gaussianAveragePolynomial_degree (t s : ℝ) {d : ℕ} {P : MvPolynomial ι ℝ}
    (hP : P ∈ MvPolynomial.restrictTotalDegree ι ℝ d) :
    gaussianAveragePolynomial ι t s P ∈ MvPolynomial.restrictTotalDegree ι ℝ d :=
  gaussianCoefficientExpectation_degree ι ι (gaussianMixedPolynomial_degree ι t s hP)

theorem gaussianAveragePolynomial_error (t s : ℝ) {d : ℕ} {P : MvPolynomial ι ℝ}
    (hP : P ∈ MvPolynomial.restrictTotalDegree ι ℝ d) :
    gaussianAveragePolynomial ι t s P - t ^ d • P ∈ polynomialDegreeLT ι ℝ d := by
  have h := gaussianCoefficientExpectation_degreeLT ι ι
    (affinePolynomialSubstitution_error ι (MvPolynomial ι ℝ) (MvPolynomial.C t)
      (fun i => s • MvPolynomial.X i) (polynomialDegreeLE_map ι ℝ MvPolynomial.C hP))
  rw [← map_pow] at h
  have hsmul (Q : MvPolynomial ι (MvPolynomial ι ℝ)) :
      (MvPolynomial.C (σ := ι) (t ^ d)) • Q = (t ^ d) • Q := by
    ext m
    simp only [MvPolynomial.coeff_smul, smul_eq_mul, MvPolynomial.coeff_C_mul]
  rw [hsmul] at h
  simpa only [map_sub, map_smul, gaussianCoefficientExpectation_map_C,
    gaussianAveragePolynomial, gaussianMixedPolynomial] using! h

theorem gaussianNoiseCLM_polynomial {t : ℝ} (ht : -1 ≤ t) (ht1 : t ≤ 1)
    (P : MvPolynomial ι ℝ) :
    gaussianNoiseCLM ι t (gaussianPolynomialL2 ι P) =
      gaussianPolynomialL2 ι (gaussianAveragePolynomial ι t (Real.sqrt (1 - t ^ 2)) P) := by
  apply Lp.ext
  filter_upwards [gaussianNoiseL2_ae ι t (gaussianPolynomialL2 ι P),
    gaussianNoise_congr_ae ι t (gaussianPolynomialL2_ae ι P),
    gaussianPolynomialL2_ae ι (gaussianAveragePolynomial ι t (Real.sqrt (1 - t ^ 2)) P)]
    with x hnoise hcongr hpoly
  exact hnoise.trans (hcongr.trans ((gaussianAveragePolynomial_eq_noise ι ht ht1 P x).symm.trans
    hpoly.symm))

theorem gaussianNoiseCLM_mem_polynomialSpace {t : ℝ} (ht : -1 ≤ t) (ht1 : t ≤ 1)
    {d : ℕ} {f : Lp ℝ 2 (coordinateGaussian ι)} (hf : f ∈ gaussianPolynomialSpace ι d) :
    gaussianNoiseCLM ι t f ∈ gaussianPolynomialSpace ι d := by
  obtain ⟨P, hP, rfl⟩ := (mem_gaussianPolynomialSpace_iff ι d f).mp hf
  exact (mem_gaussianPolynomialSpace_iff ι d _).mpr
    ⟨gaussianAveragePolynomial ι t (Real.sqrt (1 - t ^ 2)) P,
      (MvPolynomial.mem_restrictTotalDegree ι d _).mp
        (gaussianAveragePolynomial_degree ι t _ ((MvPolynomial.mem_restrictTotalDegree ι d P).mpr hP)),
      (gaussianNoiseCLM_polynomial ι ht ht1 P).symm⟩

/-- Polynomial functions of degree strictly less than `d`, including the zero space at `d = 0`. -/
def gaussianPolynomialSpaceLT (d : ℕ) : Submodule ℝ (Lp ℝ 2 (coordinateGaussian ι)) :=
  (polynomialDegreeLT ι ℝ d).map (gaussianPolynomialEmbedding ι)

@[simp] theorem gaussianPolynomialSpaceLT_zero : gaussianPolynomialSpaceLT ι 0 = ⊥ := by
  simp [gaussianPolynomialSpaceLT, polynomialDegreeLT_zero]

@[simp] theorem gaussianPolynomialSpaceLT_succ (d : ℕ) :
    gaussianPolynomialSpaceLT ι (d + 1) = gaussianPolynomialSpace ι d := by
  simp [gaussianPolynomialSpaceLT, polynomialDegreeLT_succ, gaussianPolynomialSpace]

theorem gaussianNoiseCLM_polynomial_error {t : ℝ} (ht : -1 ≤ t) (ht1 : t ≤ 1)
    {d : ℕ} {f : Lp ℝ 2 (coordinateGaussian ι)} (hf : f ∈ gaussianPolynomialSpace ι d) :
    gaussianNoiseCLM ι t f - t ^ d • f ∈ gaussianPolynomialSpaceLT ι d := by
  obtain ⟨P, hP, rfl⟩ := (mem_gaussianPolynomialSpace_iff ι d f).mp hf
  refine Submodule.mem_map.mpr
    ⟨gaussianAveragePolynomial ι t (Real.sqrt (1 - t ^ 2)) P - t ^ d • P,
      gaussianAveragePolynomial_error ι t _ ((MvPolynomial.mem_restrictTotalDegree ι d P).mpr hP), ?_⟩
  simp only [map_sub, map_smul, gaussianPolynomialEmbedding, LinearMap.coe_mk, AddHom.coe_mk,
    gaussianNoiseCLM_polynomial ι ht ht1 P]

theorem gaussianNoiseCLM_mem_polynomialSpaceLT {t : ℝ} (ht : -1 ≤ t) (ht1 : t ≤ 1)
    {d : ℕ} {f : Lp ℝ 2 (coordinateGaussian ι)} (hf : f ∈ gaussianPolynomialSpaceLT ι d) :
    gaussianNoiseCLM ι t f ∈ gaussianPolynomialSpaceLT ι d := by
  cases d with
  | zero => simp_all only [gaussianPolynomialSpaceLT_zero, Submodule.mem_bot, map_zero]
  | succ d => simpa only [gaussianPolynomialSpaceLT_succ] using!
      gaussianNoiseCLM_mem_polynomialSpace ι ht ht1 (by simpa only [gaussianPolynomialSpaceLT_succ] using! hf)

/-- The orthogonal degree-`d` Gaussian polynomial subspace. -/
def gaussianChaosSpace (d : ℕ) : Submodule ℝ (Lp ℝ 2 (coordinateGaussian ι)) :=
  gaussianPolynomialSpace ι d ⊓ (gaussianPolynomialSpaceLT ι d)ᗮ

/-- The degree filtration and symmetry identify the actual noise eigenvalue. -/
theorem gaussianNoiseCLM_chaos {t : ℝ} (ht : -1 ≤ t) (ht1 : t ≤ 1)
    {d : ℕ} {f : Lp ℝ 2 (coordinateGaussian ι)} (hf : f ∈ gaussianChaosSpace ι d) :
    gaussianNoiseCLM ι t f = t ^ d • f := by
  have hw := gaussianNoiseCLM_polynomial_error ι ht ht1 hf.1
  apply sub_eq_zero.mp
  apply (inner_self_eq_zero (𝕜 := ℝ)).mp
  rw [inner_sub_left, real_inner_smul_left]
  have hsym : inner ℝ (gaussianNoiseCLM ι t f) (gaussianNoiseCLM ι t f - t ^ d • f) =
      inner ℝ f (gaussianNoiseCLM ι t (gaussianNoiseCLM ι t f - t ^ d • f)) :=
    gaussianNoiseCLM_isSymmetric ι t f _
  rw [hsym, Submodule.inner_left_of_mem_orthogonal
    (gaussianNoiseCLM_mem_polynomialSpaceLT ι ht ht1 hw) hf.2,
    Submodule.inner_left_of_mem_orthogonal hw hf.2, mul_zero, sub_zero]

end ConvexBodyChasing

end
end BundledModule067

/- Component source: ConvexBodyChasing.OrthogonalNoise -/
section BundledModule068
/-! # A sublinear bound for the first coefficient of a contractive noise polynomial

The quantitative estimate uses orthogonality in a comparison Hilbert norm.
The eventual Gaussian application must separately establish the noise
decomposition and contraction hypotheses.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators
namespace ConvexBodyChasing

variable {ι H : Type*} [Fintype ι]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Pythagoras for a finite, pairwise orthogonal family. -/
theorem norm_sum_sq_of_orthogonal (v : ι → H)
    (horth : ∀ i j, i ≠ j → inner ℝ (v i) (v j) = 0) :
    ‖∑ i, v i‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  apply Finset.sum_congr rfl
  intro i _
  rw [inner_sum, Finset.sum_eq_single i]
  · exact real_inner_self_eq_norm_sq _
  · exact fun j _ hji => horth i j hji.symm
  · simp

/-- Bounded scalar weights contract an orthogonal sum in its Hilbert norm. -/
theorem norm_sum_smul_le_of_orthogonal (v : ι → H)
    (horth : ∀ i j, i ≠ j → inner ℝ (v i) (v j) = 0)
    (a : ι → ℝ) {C : ℝ} (hC : 0 ≤ C) (ha : ∀ i, |a i| ≤ C) :
    ‖∑ i, a i • v i‖ ≤ C * ‖∑ i, v i‖ := by
  have hw : ∀ i j, i ≠ j → inner ℝ (a i • v i) (a j • v j) = 0 := by
    exact fun i j hij => by simp [real_inner_smul_left, real_inner_smul_right, horth i j hij]
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mp
  rw [norm_sum_sq_of_orthogonal _ hw, mul_pow, norm_sum_sq_of_orthogonal v horth,
    Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => by
    simpa only [norm_smul, Real.norm_eq_abs, mul_pow] using!
      mul_le_mul_of_nonneg_right ((sq_le_sq₀ (abs_nonneg _) hC).mpr (ha i)) (sq_nonneg ‖v i‖)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

def noisePolynomial (v : Fin (n + 2) → E) (t : ℝ) : E :=
  ∑ i : Fin (n + 2), t ^ (i : ℕ) • v i

def noisePolynomialTail (v : Fin (n + 2) → E) (t : ℝ) : E :=
  ∑ i : Fin (n + 2), if 2 ≤ (i : ℕ) then t ^ (i : ℕ) • v i else 0

theorem noisePolynomial_decomposition (v : Fin (n + 2) → E) (t : ℝ) :
    noisePolynomial v t = v 0 + t • v 1 + noisePolynomialTail v t := by
  simp [noisePolynomial, noisePolynomialTail, Fin.sum_univ_succ, add_assoc]

/-- Every term of degree at least two is damped by at least `t²` in the Hilbert norm. -/
theorem norm_map_noisePolynomialTail_le (J : E →L[ℝ] H) (v : Fin (n + 2) → E)
    (horth : ∀ i j, i ≠ j → inner ℝ (J (v i)) (J (v j)) = 0)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖J (noisePolynomialTail v t)‖ ≤ t ^ 2 * ‖J (∑ i, v i)‖ := by
  have hw (i : Fin (n + 2)) : |if 2 ≤ (i : ℕ) then t ^ (i : ℕ) else 0| ≤ t ^ 2 := by
    split_ifs with hi
    · simpa [abs_of_nonneg (pow_nonneg ht _)] using! pow_le_pow_of_le_one ht ht1 hi
    · simpa using! sq_nonneg t
  simpa [noisePolynomialTail, map_sum, apply_ite, ite_smul] using!
    norm_sum_smul_le_of_orthogonal (fun i => J (v i)) horth
      (fun i => if 2 ≤ (i : ℕ) then t ^ (i : ℕ) else 0) (sq_nonneg t) hw

/-- The first coefficient is controlled by contraction and the quadratic Hilbert tail. -/
theorem noise_first_coefficient_mul_le (J : E →L[ℝ] H) {D : ℝ} (hD : 0 ≤ D)
    (hJ : ∀ x, ‖J x‖ ≤ ‖x‖) (hE : ∀ x, ‖x‖ ≤ D * ‖J x‖)
    (v : Fin (n + 2) → E)
    (horth : ∀ i j, i ≠ j → inner ℝ (J (v i)) (J (v j)) = 0)
    (hnoise : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ‖noisePolynomial v t‖ ≤ ‖∑ i, v i‖)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    t * ‖v 1‖ ≤ (2 + D * t ^ 2) * ‖∑ i, v i‖ := by
  have hzero : ‖v 0‖ ≤ ‖∑ i, v i‖ := by
    simpa [noisePolynomial, Fin.sum_univ_succ] using! hnoise 0 le_rfl zero_le_one
  have htail : ‖noisePolynomialTail v t‖ ≤ D * (t ^ 2 * ‖∑ i, v i‖) :=
    (hE _).trans (mul_le_mul_of_nonneg_left
      ((norm_map_noisePolynomialTail_le J v horth ht ht1).trans
        (mul_le_mul_of_nonneg_left (hJ _) (sq_nonneg t))) hD)
  have hidentity : t • v 1 = noisePolynomial v t - v 0 - noisePolynomialTail v t := by
    rw [noisePolynomial_decomposition]
    abel
  have htri : t * ‖v 1‖ ≤ ‖noisePolynomial v t‖ + ‖v 0‖ + ‖noisePolynomialTail v t‖ := by
    simpa only [← hidentity, norm_smul, Real.norm_of_nonneg ht] using!
      (norm_sub_le (noisePolynomial v t - v 0) (noisePolynomialTail v t)).trans
        (add_le_add (norm_sub_le (noisePolynomial v t) (v 0)) le_rfl)
  nlinarith [hnoise t ht ht1]

/-- A contraction polynomial with orthogonal coefficients has first-coefficient norm at most
`3 √D`, uniformly in its degree, when the ambient norm is within factor `D` of a Hilbert norm. -/
theorem noise_first_coefficient_le_sqrt_distortion (J : E →L[ℝ] H)
    {D : ℝ} (hD : 1 ≤ D) (hJ : ∀ x, ‖J x‖ ≤ ‖x‖)
    (hE : ∀ x, ‖x‖ ≤ D * ‖J x‖) (v : Fin (n + 2) → E)
    (horth : ∀ i j, i ≠ j → inner ℝ (J (v i)) (J (v j)) = 0)
    (hnoise : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ‖noisePolynomial v t‖ ≤ ‖∑ i, v i‖) :
    ‖v 1‖ ≤ (3 * Real.sqrt D) * ‖∑ i, v i‖ := by
  have hD0 : 0 < D := zero_lt_one.trans_le hD
  have hs : 0 < Real.sqrt D := Real.sqrt_pos.mpr hD0
  have hs1 : 1 ≤ Real.sqrt D := by simpa using! Real.sqrt_le_sqrt hD
  have ht1 : (Real.sqrt D)⁻¹ ≤ 1 := by simpa using! (div_le_one hs).mpr hs1
  have hinv : D * ((Real.sqrt D)⁻¹) ^ 2 = 1 := by
    simp [inv_pow, Real.sq_sqrt hD0.le, hD0.ne']
  have hb := noise_first_coefficient_mul_le J hD0.le hJ hE v horth hnoise
    (inv_pos.mpr hs).le ht1
  simpa only [hinv, show (2 : ℝ) + 1 = 3 by norm_num, ← mul_assoc,
    mul_inv_cancel₀ hs.ne', one_mul, mul_comm (Real.sqrt D) 3] using!
    mul_le_mul_of_nonneg_left hb hs.le

end ConvexBodyChasing

end
end BundledModule068

/- Component source: ConvexBodyChasing.GaussianChaos -/
section BundledModule069
/-! # Finite orthogonal Gaussian polynomial decomposition

Every bounded-degree Gaussian polynomial splits into orthogonal degree pieces.
This finite decomposition uses the proved degree filtration and its noise
eigenvalues; it does not assume density of polynomials in Gaussian L².
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace ConvexBodyChasing

variable (ι : Type*) [Fintype ι]

@[simp] theorem gaussianChaosSpace_zero : gaussianChaosSpace ι 0 = gaussianPolynomialSpace ι 0 := by
  simp [gaussianChaosSpace]

instance gaussianChaosSpace_finiteDimensional (d : ℕ) :
    FiniteDimensional ℝ (gaussianChaosSpace ι d) := by
  unfold gaussianChaosSpace
  infer_instance

/-- The canonical orthogonal projection onto the degree-`d` Gaussian polynomial space. -/
def gaussianChaosProjection (d : ℕ) :
    Lp ℝ 2 (coordinateGaussian ι) →L[ℝ] Lp ℝ 2 (coordinateGaussian ι) :=
  (gaussianChaosSpace ι d).starProjection

theorem gaussianChaosProjection_mem (d : ℕ) (f : Lp ℝ 2 (coordinateGaussian ι)) :
    gaussianChaosProjection ι d f ∈ gaussianChaosSpace ι d :=
  (gaussianChaosSpace ι d).starProjection_apply_mem f

theorem gaussianPolynomialSpace_le_LT {d e : ℕ} (h : d < e) :
    gaussianPolynomialSpace ι d ≤ gaussianPolynomialSpaceLT ι e :=
  Submodule.map_mono (polynomialDegreeLE_le_lt ι ℝ h)

theorem gaussianChaosSpace_inner_zero_of_lt {d e : ℕ} (h : d < e)
    {f g : Lp ℝ 2 (coordinateGaussian ι)}
    (hf : f ∈ gaussianChaosSpace ι d) (hg : g ∈ gaussianChaosSpace ι e) :
    inner ℝ f g = 0 := by
  exact Submodule.inner_right_of_mem_orthogonal (gaussianPolynomialSpace_le_LT ι h hf.1) hg.2

theorem gaussianChaosSpace_inner_zero {d e : ℕ} (h : d ≠ e)
    {f g : Lp ℝ 2 (coordinateGaussian ι)}
    (hf : f ∈ gaussianChaosSpace ι d) (hg : g ∈ gaussianChaosSpace ι e) :
    inner ℝ f g = 0 := by
  rcases lt_or_gt_of_ne h with hlt | hgt
  · exact gaussianChaosSpace_inner_zero_of_lt ι hlt hf hg
  · exact (real_inner_comm g f).trans (gaussianChaosSpace_inner_zero_of_lt ι hgt hg hf)

theorem gaussianPolynomialSpace_succ (d : ℕ) :
    gaussianPolynomialSpace ι d ⊔ gaussianChaosSpace ι (d + 1) =
      gaussianPolynomialSpace ι (d + 1) := by
  simpa only [gaussianChaosSpace, gaussianPolynomialSpaceLT_succ, inf_comm] using!
    Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection
      (gaussianPolynomialSpace_mono ι (Nat.le_succ d))

theorem exists_gaussianChaos_decomposition {d : ℕ} {f : Lp ℝ 2 (coordinateGaussian ι)}
    (hf : f ∈ gaussianPolynomialSpace ι d) :
    ∃ v : Fin (d + 1) → Lp ℝ 2 (coordinateGaussian ι),
      (∀ i, v i ∈ gaussianChaosSpace ι i.val) ∧ ∑ i, v i = f := by
  induction d generalizing f with
  | zero => exact ⟨fun _ => f, by simpa using! hf, by simp⟩
  | succ d ih =>
    rw [← gaussianPolynomialSpace_succ, Submodule.mem_sup] at hf
    obtain ⟨g, hg, h, hh, rfl⟩ := hf
    obtain ⟨v, hv, rfl⟩ := ih hg
    refine ⟨Fin.snoc v h, ?_, ?_⟩
    · exact fun i => Fin.lastCases (by simpa using! hh) (fun j => by simpa using! hv j) i
    · simp [Fin.sum_univ_castSucc]

theorem gaussianChaosProjection_eq_self {d : ℕ} {f : Lp ℝ 2 (coordinateGaussian ι)}
    (hf : f ∈ gaussianChaosSpace ι d) : gaussianChaosProjection ι d f = f :=
  (gaussianChaosSpace ι d).starProjection_eq_self_iff.mpr hf

theorem gaussianChaosProjection_eq_zero_of_ne {d e : ℕ} (h : d ≠ e)
    {f : Lp ℝ 2 (coordinateGaussian ι)} (hf : f ∈ gaussianChaosSpace ι e) :
    gaussianChaosProjection ι d f = 0 := by
  change f ∈ (gaussianChaosSpace ι d).starProjection.ker
  rw [Submodule.ker_starProjection]
  exact fun g hg => gaussianChaosSpace_inner_zero ι h hg hf

theorem gaussianChaosProjection_sum {n : ℕ} (v : Fin n → Lp ℝ 2 (coordinateGaussian ι))
    (hv : ∀ i, v i ∈ gaussianChaosSpace ι i.val) (i : Fin n) :
    gaussianChaosProjection ι i.val (∑ j, v j) = v i := by
  rw [map_sum, Finset.sum_eq_single i]
  · exact gaussianChaosProjection_eq_self ι (hv i)
  · exact fun j _ hji => gaussianChaosProjection_eq_zero_of_ne ι
      (fun hij => hji (Fin.ext hij.symm)) (hv j)
  · simp

theorem sum_gaussianChaosProjection {d : ℕ} {f : Lp ℝ 2 (coordinateGaussian ι)}
    (hf : f ∈ gaussianPolynomialSpace ι d) :
    ∑ i : Fin (d + 1), gaussianChaosProjection ι i.val f = f := by
  obtain ⟨v, hv, rfl⟩ := exists_gaussianChaos_decomposition ι hf
  exact Finset.sum_congr rfl (fun i _ => gaussianChaosProjection_sum ι v hv i)



theorem gaussianChaosProjection_truncate {d e : ℕ} (h : d ≤ e)
    (f : Lp ℝ 2 (coordinateGaussian ι)) :
    gaussianChaosProjection ι d ((gaussianPolynomialSpace ι e).starProjection f) =
      gaussianChaosProjection ι d f := by
  exact congrArg Subtype.val (Submodule.orthogonalProjection_starProjection_of_le
    (U := gaussianChaosSpace ι d) (V := gaussianPolynomialSpace ι e)
    (fun _ hf => gaussianPolynomialSpace_mono ι h hf.1) f)

theorem sum_gaussianChaosProjection_eq_truncate (d : ℕ) (f : Lp ℝ 2 (coordinateGaussian ι)) :
    ∑ i : Fin (d + 1), gaussianChaosProjection ι i.val f =
      (gaussianPolynomialSpace ι d).starProjection f := by
  have h := sum_gaussianChaosProjection ι ((gaussianPolynomialSpace ι d).starProjection_apply_mem f)
  simpa only [gaussianChaosProjection_truncate ι (Nat.le_of_lt_succ (Fin.isLt _))] using! h



end ConvexBodyChasing

end
end BundledModule069

/- Component source: ConvexBodyChasing.MomentDetermination -/
section BundledModule070
/-! # Determination by moments under exponential integrability

This provides the analytic uniqueness step for Gaussian polynomial density.
The required exponential integrability is stated explicitly here and must be
proved for the measures to which the result is applied.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Topology
namespace ConvexBodyChasing

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  {μ : Measure Ω} {ν : Measure Ω'} {X : Ω → ℝ} {Y : Ω' → ℝ}

theorem integrableExpSet_eq_univ_of_forall
    (h : ∀ t : ℝ, Integrable (fun x => Real.exp (t * X x)) μ) :
    integrableExpSet X μ = Set.univ := by
  exact Set.eq_univ_of_forall h

theorem mgf_eq_of_moments
    (hX : ∀ t : ℝ, Integrable (fun x => Real.exp (t * X x)) μ)
    (hY : ∀ t : ℝ, Integrable (fun y => Real.exp (t * Y y)) ν)
    (hm : ∀ n : ℕ, (∫ x, X x ^ n ∂μ) = ∫ y, Y y ^ n ∂ν) :
    mgf X μ = mgf Y ν := by
  have hXu := integrableExpSet_eq_univ_of_forall hX
  have hYu := integrableExpSet_eq_univ_of_forall hY
  apply AnalyticOnNhd.eq_of_eventuallyEq
    (by simpa only [hXu, interior_univ] using! (analyticOnNhd_mgf (X := X) (μ := μ)))
    (by simpa only [hYu, interior_univ] using! (analyticOnNhd_mgf (X := Y) (μ := ν)))
    (z₀ := (0 : ℝ))
  have hpX : HasFPowerSeriesAt (mgf X μ)
      (FormalMultilinearSeries.ofScalars ℝ (fun n => (∫ x, X x ^ n ∂μ) / n.factorial)) 0 := by
    simpa using! (hasFPowerSeriesAt_mgf (X := X) (μ := μ) (v := 0) (by simp [hXu]))
  have hpY : HasFPowerSeriesAt (mgf Y ν)
      (FormalMultilinearSeries.ofScalars ℝ (fun n => (∫ x, X x ^ n ∂μ) / n.factorial)) 0 := by
    simpa only [zero_mul, Real.exp_zero, mul_one, hm] using!
      (hasFPowerSeriesAt_mgf (X := Y) (μ := ν) (v := 0) (by simp [hYu]))
  exact hpX.eventually_hasSum_sub.mp (hpY.eventually_hasSum_sub.mono (fun _ hY hX => hX.unique hY))

theorem complexMGF_eq_of_moments [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hX : ∀ t : ℝ, Integrable (fun x => Real.exp (t * X x)) μ)
    (hY : ∀ t : ℝ, Integrable (fun y => Real.exp (t * Y y)) ν)
    (hm : ∀ n : ℕ, (∫ x, X x ^ n ∂μ) = ∫ y, Y y ^ n ∂ν) :
    complexMGF X μ = complexMGF Y ν := by
  have hmgf := mgf_eq_of_moments hX hY hm
  have hmass : μ.real Set.univ = ν.real Set.univ := by simpa using! hm 0
  have hzero : μ = 0 ↔ ν = 0 := by
    rw [← Measure.measure_univ_eq_zero, ← measureReal_eq_zero_iff, hmass,
      measureReal_eq_zero_iff, Measure.measure_univ_eq_zero]
  exact funext (fun z => eqOn_complexMGF_of_mgf' hmgf hzero
    (by simp [integrableExpSet_eq_univ_of_forall hX]))



theorem measure_eq_of_dual_moments {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]
    {η ζ : Measure E} [IsFiniteMeasure η] [IsFiniteMeasure ζ]
    (hη : ∀ (L : E →L[ℝ] ℝ) (t : ℝ), Integrable (fun x => Real.exp (t * L x)) η)
    (hζ : ∀ (L : E →L[ℝ] ℝ) (t : ℝ), Integrable (fun x => Real.exp (t * L x)) ζ)
    (hm : ∀ (L : E →L[ℝ] ℝ) (n : ℕ), (∫ x, L x ^ n ∂η) = ∫ x, L x ^ n ∂ζ) :
    η = ζ := by
  apply Measure.ext_of_charFunDual
  funext L
  simpa only [charFunDual_apply, complexMGF, mul_comm] using!
    congrFun (complexMGF_eq_of_moments (hη L) (hζ L) (hm L)) Complex.I

end ConvexBodyChasing

end
end BundledModule070

/- Component source: ConvexBodyChasing.L2MomentUniqueness -/
section BundledModule071
/-! # Uniqueness from vanishing weighted moments

An L² function with vanishing linear-functional moments is zero when those
linear functionals have the required exponential moments. The proof compares
two finite positive measures and uses the proved moment-determination theorem.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace ConvexBodyChasing

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem integral_withDensity_ofReal_nonneg {g : Ω → ℝ}
    (hg : AEMeasurable g μ) (hgn : ∀ x, 0 ≤ g x) (h : Ω → ℝ) :
    (∫ x, h x ∂μ.withDensity (fun x => ENNReal.ofReal (g x))) = ∫ x, g x * h x ∂μ := by
  simpa only [ENNReal.toReal_ofReal (hgn _), smul_eq_mul] using!
    integral_withDensity_eq_integral_toReal_smul₀ hg.ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)) h

theorem integrable_withDensity_of_memLp_two {g h : Ω → ℝ}
    (hg : MemLp g 2 μ) (hgn : ∀ x, 0 ≤ g x) (hh : MemLp h 2 μ) :
    Integrable h (μ.withDensity (fun x => ENNReal.ofReal (g x))) := by
  apply (integrable_withDensity_iff_integrable_smul₀' hg.1.aemeasurable.ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))).mpr
  simpa only [ENNReal.toReal_ofReal (hgn _), smul_eq_mul] using! hg.integrable_mul hh

theorem ae_eq_zero_of_l2_dual_moments {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]
    {η : Measure E} [IsFiniteMeasure η] {f : E → ℝ} (hf : MemLp f 2 η)
    (hexp : ∀ (L : E →L[ℝ] ℝ) (t : ℝ), MemLp (fun x => Real.exp (t * L x)) 2 η)
    (hpow : ∀ (L : E →L[ℝ] ℝ) (n : ℕ), MemLp (fun x => L x ^ n) 2 η)
    (hm : ∀ (L : E →L[ℝ] ℝ) (n : ℕ), (∫ x, f x * L x ^ n ∂η) = 0) :
    f =ᵐ[η] 0 := by
  have ha : MemLp (fun x => ‖f x‖ + f x) 2 η := hf.norm.add hf
  have han (x : E) : 0 ≤ ‖f x‖ + f x := by
    simpa [Real.norm_eq_abs, add_comm] using! add_le_add_right (neg_le_abs (f x)) (f x)
  letI : IsFiniteMeasure (η.withDensity (fun x => ENNReal.ofReal (‖f x‖ + f x))) :=
    isFiniteMeasure_withDensity_ofReal (ha.integrable (by norm_num)).hasFiniteIntegral
  letI : IsFiniteMeasure (η.withDensity (fun x => ENNReal.ofReal ‖f x‖)) :=
    isFiniteMeasure_withDensity_ofReal (hf.norm.integrable (by norm_num)).hasFiniteIntegral
  have hmeas : η.withDensity (fun x => ENNReal.ofReal (‖f x‖ + f x)) =
      η.withDensity (fun x => ENNReal.ofReal ‖f x‖) := by
    refine measure_eq_of_dual_moments
      (fun L t => integrable_withDensity_of_memLp_two ha han (hexp L t))
      (fun L t => integrable_withDensity_of_memLp_two hf.norm (fun x => norm_nonneg _) (hexp L t)) ?_
    intro L n
    simp only [integral_withDensity_ofReal_nonneg ha.1.aemeasurable han,
      integral_withDensity_ofReal_nonneg hf.norm.1.aemeasurable (fun x => norm_nonneg (f x)),
      add_mul]
    exact (integral_add (hf.norm.integrable_mul (hpow L n)) (hf.integrable_mul (hpow L n))).trans
      (by simp only [Pi.mul_apply, hm, add_zero])
  have hae := (withDensity_eq_iff_of_sigmaFinite ha.1.aemeasurable.ennreal_ofReal
    hf.norm.1.aemeasurable.ennreal_ofReal).mp hmeas
  filter_upwards [hae] with x hx
  simpa only [ENNReal.toReal_ofReal (han x), ENNReal.toReal_ofReal (norm_nonneg (f x)), add_eq_left]
    using! congrArg ENNReal.toReal hx

end ConvexBodyChasing

end
end BundledModule071

/- Component source: ConvexBodyChasing.GaussianPolynomialDensity -/
section BundledModule072
/-! # Density of Gaussian polynomial functions

Polynomial orthogonality gives vanishing moments against powers of every
linear functional. Gaussian exponential integrability then determines the
two positive measures used in the L² moment-uniqueness argument.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Topology
namespace ConvexBodyChasing

variable (ι : Type*) [Fintype ι]

theorem coordinateGaussian_integrable_exp_linear (L : (ι → ℝ) →L[ℝ] ℝ) (t : ℝ) :
    Integrable (fun x => Real.exp (t * L x)) (coordinateGaussian ι) := by
  have h : Integrable (fun z : ℝ => Real.exp (t * z)) ((coordinateGaussian ι).map L) := by
    simpa only [IsGaussian.map_eq_gaussianReal L] using! integrable_exp_mul_gaussianReal t
  exact h.comp_measurable L.continuous.measurable

theorem coordinateGaussian_memLp_exp_linear (L : (ι → ℝ) →L[ℝ] ℝ) (t : ℝ) :
    MemLp (fun x => Real.exp (t * L x)) 2 (coordinateGaussian ι) := by
  apply (memLp_two_iff_integrable_sq (by fun_prop)).mpr
  simpa only [← Real.exp_nat_mul, Nat.cast_ofNat, mul_assoc] using!
    coordinateGaussian_integrable_exp_linear ι L (2 * t)

theorem exists_polynomial_eval_eq_linear (L : (ι → ℝ) →L[ℝ] ℝ) :
    ∃ P : MvPolynomial ι ℝ, ∀ x : ι → ℝ, MvPolynomial.eval x P = L x := by
  classical
  refine ⟨∑ i, (L.comp (ContinuousLinearMap.single ℝ (fun _ : ι => ℝ) i)) 1 • MvPolynomial.X i, ?_⟩
  intro x
  simp only [map_sum, MvPolynomial.smul_eval, MvPolynomial.eval_X]
  exact (Finset.sum_congr rfl (fun i _ => by
    simpa only [smul_eq_mul, mul_one, mul_comm] using!
      ((L.comp (ContinuousLinearMap.single ℝ (fun _ : ι => ℝ) i)).map_smul (x i) 1).symm)).trans
    (ContinuousLinearMap.sum_comp_single ℝ (fun _ : ι => ℝ) L x)

theorem coordinateGaussian_memLp_linear_pow (L : (ι → ℝ) →L[ℝ] ℝ) (n : ℕ) :
    MemLp (fun x => L x ^ n) 2 (coordinateGaussian ι) := by
  obtain ⟨P, hP⟩ := exists_polynomial_eval_eq_linear ι L
  simpa only [map_pow, hP] using! coordinateGaussian_memLp_polynomial ι (P ^ n) 2 (by norm_num)

theorem inner_gaussianPolynomialL2 (f : Lp ℝ 2 (coordinateGaussian ι)) (P : MvPolynomial ι ℝ) :
    inner ℝ f (gaussianPolynomialL2 ι P) =
      ∫ x, f x * MvPolynomial.eval x P ∂coordinateGaussian ι := by
  rw [L2.inner_def]
  apply integral_congr_ae
  exact (gaussianPolynomialL2_ae ι P).mono (fun x hx => by
    simp only [hx, RCLike.inner_apply, conj_trivial, mul_comm])

theorem eq_zero_of_inner_gaussianPolynomials (f : Lp ℝ 2 (coordinateGaussian ι))
    (hf : ∀ P : MvPolynomial ι ℝ, inner ℝ f (gaussianPolynomialL2 ι P) = 0) :
    f = 0 := by
  have hz : (fun x => f x) =ᵐ[coordinateGaussian ι] 0 := by
    apply ae_eq_zero_of_l2_dual_moments (Lp.memLp f)
      (coordinateGaussian_memLp_exp_linear ι) (coordinateGaussian_memLp_linear_pow ι)
    intro L n
    obtain ⟨P, hP⟩ := exists_polynomial_eval_eq_linear ι L
    simpa only [inner_gaussianPolynomialL2, map_pow, hP] using! hf (P ^ n)
  exact Lp.ext (hz.trans (Lp.coeFn_zero ℝ 2 (coordinateGaussian ι)).symm)

theorem gaussianPolynomialEmbedding_orthogonal_eq_bot :
    (LinearMap.range (gaussianPolynomialEmbedding ι))ᗮ = ⊥ := by
  refine le_antisymm (fun f hf => ?_) bot_le
  apply eq_zero_of_inner_gaussianPolynomials ι f
  exact fun P => Submodule.inner_left_of_mem_orthogonal
    (K := LinearMap.range (gaussianPolynomialEmbedding ι)) ⟨P, rfl⟩ hf

/-- Polynomial evaluations are dense in the actual Gaussian `L²` space. -/
theorem gaussianPolynomialL2_denseRange : DenseRange (gaussianPolynomialL2 ι) := by
  change Dense (LinearMap.range (gaussianPolynomialEmbedding ι) : Set (Lp ℝ 2 (coordinateGaussian ι)))
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  rw [← Submodule.orthogonal_orthogonal_eq_closure,
    gaussianPolynomialEmbedding_orthogonal_eq_bot, Submodule.bot_orthogonal_eq_top]

theorem iSup_gaussianPolynomialSpace :
    (⨆ d : ℕ, gaussianPolynomialSpace ι d) = LinearMap.range (gaussianPolynomialEmbedding ι) := by
  apply le_antisymm
  · exact iSup_le (fun _ _ ⟨P, _, hP⟩ => ⟨P, hP⟩)
  · rintro _ ⟨P, rfl⟩
    exact le_iSup (gaussianPolynomialSpace ι) P.totalDegree
      (Submodule.mem_map.mpr ⟨P, (MvPolynomial.mem_restrictTotalDegree ι _ P).mpr le_rfl, rfl⟩)

theorem gaussianPolynomialProjection_tendsto (f : Lp ℝ 2 (coordinateGaussian ι)) :
    Filter.Tendsto (fun d : ℕ => (gaussianPolynomialSpace ι d).starProjection f)
      Filter.atTop (𝓝 f) := by
  apply Submodule.starProjection_tendsto_self (gaussianPolynomialSpace ι)
    (gaussianPolynomialSpace_mono ι) f
  rw [iSup_gaussianPolynomialSpace]
  exact ((Submodule.dense_iff_topologicalClosure_eq_top
    (s := LinearMap.range (gaussianPolynomialEmbedding ι))).mp (gaussianPolynomialL2_denseRange ι)).ge

/-- The scalar Gaussian chaos expansion converges in `L²`. -/
theorem gaussianChaosProjection_sum_tendsto (f : Lp ℝ 2 (coordinateGaussian ι)) :
    Filter.Tendsto (fun d : ℕ => ∑ i : Fin (d + 1), gaussianChaosProjection ι i.val f)
      Filter.atTop (𝓝 f) := by
  simpa only [sum_gaussianChaosProjection_eq_truncate] using! gaussianPolynomialProjection_tendsto ι f



end ConvexBodyChasing

end
end BundledModule072

/- Component source: ConvexBodyChasing.L2Tensor -/
section BundledModule073
/-! # Extending scalar L² operators to finite-dimensional vector-valued L²

The extension is defined through a finite basis, using actual continuous linear
maps on L². Its interaction with every continuous linear functional is proved.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open MeasureTheory Module
open scoped BigOperators
namespace ConvexBodyChasing

variable {Ω E F κ : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [Fintype κ]

def l2Vector (x : E) : Lp ℝ 2 μ →L[ℝ] Lp E 2 μ :=
  (ContinuousLinearMap.toSpanSingleton ℝ x).compLpL 2 μ

def l2Coordinate (b : Basis κ ℝ E) (i : κ) : Lp E 2 μ →L[ℝ] Lp ℝ 2 μ :=
  ((ContinuousLinearMap.proj i).comp b.equivFunL.toContinuousLinearMap).compLpL 2 μ

theorem l2Vector_ae (x : E) (f : Lp ℝ 2 μ) :
    l2Vector μ x f =ᵐ[μ] fun a => f a • x :=
  (ContinuousLinearMap.toSpanSingleton ℝ x).coeFn_compLpL f

theorem l2Coordinate_ae (b : Basis κ ℝ E) (i : κ) (f : Lp E 2 μ) :
    l2Coordinate μ b i f =ᵐ[μ] fun a => b.equivFun (f a) i :=
  ((ContinuousLinearMap.proj i).comp b.equivFunL.toContinuousLinearMap).coeFn_compLpL f

theorem compLpL_l2Vector (L : E →L[ℝ] F) (x : E) (f : Lp ℝ 2 μ) :
    L.compLpL 2 μ (l2Vector μ x f) = l2Vector μ (L x) f := by
  apply Lp.ext
  filter_upwards [L.coeFn_compLpL (l2Vector μ x f), l2Vector_ae μ x f,
    l2Vector_ae μ (L x) f] with a ha hb hc
  simp only [ha, hb, hc, map_smul]

theorem l2Vector_scalar (c : ℝ) (f : Lp ℝ 2 μ) : l2Vector μ c f = c • f := by
  apply Lp.ext
  filter_upwards [l2Vector_ae μ c f, Lp.coeFn_smul c f] with a ha hb
  simp only [ha, hb, Pi.smul_apply, smul_eq_mul, mul_comm]

omit [NormedSpace ℝ E] [Fintype κ] in
theorem l2_sum_ae (s : Finset κ) (f : κ → Lp E 2 μ) :
    (∑ i ∈ s, f i : Lp E 2 μ) =ᵐ[μ] fun a => ∑ i ∈ s, f i a := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using! Lp.coeFn_zero E 2 μ
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi, Pi.add_apply] using!
      (Lp.coeFn_add (f i) (∑ j ∈ s, f j)).trans (Filter.EventuallyEq.add Filter.EventuallyEq.rfl ih)

theorem sum_l2Vector_coordinate (b : Basis κ ℝ E) (f : Lp E 2 μ) :
    ∑ i, l2Vector μ (b i) (l2Coordinate μ b i f) = f := by
  apply Lp.ext
  filter_upwards [l2_sum_ae μ Finset.univ (fun i => l2Vector μ (b i) (l2Coordinate μ b i f)),
    Filter.eventually_all.mpr (fun i => l2Vector_ae μ (b i) (l2Coordinate μ b i f)),
    Filter.eventually_all.mpr (fun i => l2Coordinate_ae μ b i f)] with a ha hb hc
  simpa only [ha, hb, hc] using! b.sum_equivFun (f a)

def l2Tensor (b : Basis κ ℝ E) (S : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) :
    Lp E 2 μ →L[ℝ] Lp E 2 μ :=
  ∑ i, (l2Vector μ (b i)).comp (S.comp (l2Coordinate μ b i))

theorem l2Tensor_apply (b : Basis κ ℝ E) (S : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (f : Lp E 2 μ) : l2Tensor μ b S f = ∑ i, l2Vector μ (b i) (S (l2Coordinate μ b i f)) := by
  simp only [l2Tensor, ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply]

theorem functional_l2Tensor (b : Basis κ ℝ E) (S : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (L : E →L[ℝ] ℝ) (f : Lp E 2 μ) :
    L.compLpL 2 μ (l2Tensor μ b S f) = S (L.compLpL 2 μ f) := by
  rw [l2Tensor_apply, map_sum]
  simp only [compLpL_l2Vector, l2Vector_scalar, ← map_smul S, ← map_sum S]
  exact congrArg S (by
    simpa only [map_sum, compLpL_l2Vector, l2Vector_scalar] using!
      (congrArg (L.compLpL 2 μ) (sum_l2Vector_coordinate μ b f)))

theorem inner_l2Vector {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (x y : H) (f g : Lp ℝ 2 μ) :
    inner ℝ (l2Vector μ x f) (l2Vector μ y g) = inner ℝ f g * inner ℝ x y := by
  rw [L2.inner_def, L2.inner_def, ← integral_mul_const]
  apply integral_congr_ae
  filter_upwards [l2Vector_ae μ x f, l2Vector_ae μ y g] with a ha hb
  simp only [ha, hb, real_inner_smul_left, real_inner_smul_right,
    RCLike.inner_apply, conj_trivial, mul_assoc]



theorem norm_le_compLpL_of_bound (L : E →L[ℝ] F) {C : ℝ}
    (h : ∀ x, ‖x‖ ≤ C * ‖L x‖) (f : Lp E 2 μ) :
    ‖f‖ ≤ C * ‖L.compLpL 2 μ f‖ := by
  exact Lp.norm_le_mul_norm_of_ae_le_mul
    ((L.coeFn_compLpL f).mono (fun a ha => by simpa only [ha] using! h (f a)))

theorem l2_ext_coordinate (b : Basis κ ℝ E) {f g : Lp E 2 μ}
    (h : ∀ i, l2Coordinate μ b i f = l2Coordinate μ b i g) : f = g := by
  exact (sum_l2Vector_coordinate μ b f).symm.trans
    ((Finset.sum_congr rfl (fun i _ => congrArg (l2Vector μ (b i)) (h i))).trans
      (sum_l2Vector_coordinate μ b g))

theorem l2_ext_functional (b : Basis κ ℝ E) {f g : Lp E 2 μ}
    (h : ∀ L : E →L[ℝ] ℝ, L.compLpL 2 μ f = L.compLpL 2 μ g) : f = g := by
  exact l2_ext_coordinate μ b (fun i => h ((ContinuousLinearMap.proj i).comp
    b.equivFunL.toContinuousLinearMap))





end ConvexBodyChasing

end
end BundledModule073

/- Component source: ConvexBodyChasing.GaussianVectorChaos -/
section BundledModule074
/-! # Finite-dimensional vector-valued Gaussian chaos

Scalar degree projections extend through any finite basis. Gaussian noise
commutes with continuous linear maps, and distinct degrees are orthogonal
after any continuous linear map into a Hilbert space.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open MeasureTheory Module
open scoped BigOperators Topology
namespace ConvexBodyChasing

variable (ι : Type*) [Fintype ι]
variable {E F κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] [Fintype κ]

theorem gaussianNoise_comp_linear_ae (L : E →L[ℝ] F) (t : ℝ)
    {f : (ι → ℝ) → E} (hf : MemLp f 2 (coordinateGaussian ι)) :
    gaussianNoise ι t (fun x => L (f x)) =ᵐ[coordinateGaussian ι]
      fun x => L (gaussianNoise ι t f x) := by
  exact ((hf.comp_measurePreserving (gaussianNoiseMix_preserving ι t)).integrable
    (by norm_num)).prod_right_ae.mono (fun _ h => L.integral_comp_comm h)

theorem gaussianNoiseCLM_compLpL (L : E →L[ℝ] F) (t : ℝ)
    (f : Lp E 2 (coordinateGaussian ι)) :
    gaussianNoiseCLM ι t (L.compLpL 2 (coordinateGaussian ι) f) =
      L.compLpL 2 (coordinateGaussian ι) (gaussianNoiseCLM ι t f) := by
  apply Lp.ext
  exact (gaussianNoiseL2_ae ι t _).trans
    ((gaussianNoise_congr_ae ι t (L.coeFn_compLpL f)).trans
      ((gaussianNoise_comp_linear_ae ι L t (Lp.memLp f)).trans
        (Filter.EventuallyEq.trans
          (Filter.EventuallyEq.symm ((gaussianNoiseL2_ae ι t f).mono (fun _ h => congrArg L h)))
          (L.coeFn_compLpL (gaussianNoiseCLM ι t f)).symm)))

theorem gaussianNoiseCLM_l2Vector (x : E) (t : ℝ)
    (f : Lp ℝ 2 (coordinateGaussian ι)) :
    gaussianNoiseCLM ι t (l2Vector (coordinateGaussian ι) x f) =
      l2Vector (coordinateGaussian ι) x (gaussianNoiseCLM ι t f) :=
  gaussianNoiseCLM_compLpL ι (ContinuousLinearMap.toSpanSingleton ℝ x) t f

/-- Degree projection extended to vector-valued L² using a finite basis. -/
def gaussianVectorChaos (b : Basis κ ℝ E) (d : ℕ) :
    Lp E 2 (coordinateGaussian ι) →L[ℝ] Lp E 2 (coordinateGaussian ι) :=
  l2Tensor (coordinateGaussian ι) b (gaussianChaosProjection ι d)

theorem gaussianNoiseCLM_vectorChaos (b : Basis κ ℝ E) {t : ℝ}
    (ht : -1 ≤ t) (ht1 : t ≤ 1) (d : ℕ) (f : Lp E 2 (coordinateGaussian ι)) :
    gaussianNoiseCLM ι t (gaussianVectorChaos ι b d f) = t ^ d • gaussianVectorChaos ι b d f := by
  simp only [gaussianVectorChaos, l2Tensor_apply, map_sum, Finset.smul_sum, gaussianNoiseCLM_l2Vector]
  exact Finset.sum_congr rfl (fun i _ =>
    (congrArg (l2Vector (coordinateGaussian ι) (b i))
      (gaussianNoiseCLM_chaos ι ht ht1 (gaussianChaosProjection_mem ι d _))).trans
        (map_smul _ _ _))

omit [CompleteSpace E] in
theorem gaussianVectorChaos_inner_map_zero {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (J : E →L[ℝ] H) (b : Basis κ ℝ E) {d e : ℕ} (h : d ≠ e)
    (f g : Lp E 2 (coordinateGaussian ι)) :
    inner ℝ (J.compLpL 2 (coordinateGaussian ι) (gaussianVectorChaos ι b d f))
      (J.compLpL 2 (coordinateGaussian ι) (gaussianVectorChaos ι b e g)) = 0 := by
  simp only [gaussianVectorChaos, l2Tensor_apply, map_sum, compLpL_l2Vector,
    sum_inner, inner_sum, inner_l2Vector]
  simp only [gaussianChaosSpace_inner_zero ι h (gaussianChaosProjection_mem ι d _)
    (gaussianChaosProjection_mem ι e _), zero_mul, Finset.sum_const_zero]

omit [CompleteSpace E] in
theorem sum_gaussianVectorChaos (b : Basis κ ℝ E) (n : ℕ)
    (f : Lp E 2 (coordinateGaussian ι)) :
    ∑ d : Fin n, gaussianVectorChaos ι b d.val f =
      ∑ i, l2Vector (coordinateGaussian ι) (b i)
        (∑ d : Fin n, gaussianChaosProjection ι d.val (l2Coordinate (coordinateGaussian ι) b i f)) := by
  simp only [gaussianVectorChaos, l2Tensor_apply, map_sum]
  exact Finset.sum_comm

omit [CompleteSpace E] in
theorem gaussianVectorChaos_sum_tendsto (b : Basis κ ℝ E)
    (f : Lp E 2 (coordinateGaussian ι)) :
    Filter.Tendsto (fun d : ℕ => ∑ i : Fin (d + 1), gaussianVectorChaos ι b i.val f)
      Filter.atTop (𝓝 f) := by
  have h := tendsto_finset_sum Finset.univ (fun i (_ : i ∈ Finset.univ) =>
    ((l2Vector (coordinateGaussian ι) (b i)).continuous.tendsto _).comp
      (gaussianChaosProjection_sum_tendsto ι (l2Coordinate (coordinateGaussian ι) b i f)))
  simpa only [Function.comp_def, ← sum_gaussianVectorChaos, sum_l2Vector_coordinate] using! h

theorem gaussianNoiseCLM_vectorChaos_sum (b : Basis κ ℝ E) {t : ℝ}
    (ht : -1 ≤ t) (ht1 : t ≤ 1) (n : ℕ) (f : Lp E 2 (coordinateGaussian ι)) :
    gaussianNoiseCLM ι t (∑ i : Fin (n + 2), gaussianVectorChaos ι b i.val f) =
      noisePolynomial (fun i : Fin (n + 2) => gaussianVectorChaos ι b i.val f) t := by
  simp only [map_sum, noisePolynomial, gaussianNoiseCLM_vectorChaos ι b ht ht1]





end ConvexBodyChasing

end
end BundledModule074

/- Component source: ConvexBodyChasing.GaussianProjectionBound -/
section BundledModule075
/-! # Gaussian first-chaos projection bound in a finite-dimensional norm

The actual Gaussian noise contraction and convergent vector chaos expansion
instantiate the orthogonal-polynomial estimate. The distortion hypotheses
compare the specified norm with a Hilbert norm and do not assume a projection
estimate or any Gaussian decomposition.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open MeasureTheory Module
open scoped BigOperators Topology
namespace ConvexBodyChasing

variable (ι : Type*) [Fintype ι]
variable {E H κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Fintype κ]

theorem gaussianVectorChaos_first_norm_le_partial (b : Basis κ ℝ E) (J : E →L[ℝ] H)
    {D : ℝ} (hD : 1 ≤ D) (hJ : ∀ x, ‖J x‖ ≤ ‖x‖) (hE : ∀ x, ‖x‖ ≤ D * ‖J x‖)
    (n : ℕ) (f : Lp E 2 (coordinateGaussian ι)) :
    ‖gaussianVectorChaos ι b 1 f‖ ≤ 3 * Real.sqrt D *
      ‖∑ i : Fin (n + 2), gaussianVectorChaos ι b i.val f‖ := by
  apply noise_first_coefficient_le_sqrt_distortion (J.compLpL 2 (coordinateGaussian ι)) hD
    (v := fun i : Fin (n + 2) => gaussianVectorChaos ι b i.val f)
  case hnoise =>
    exact fun t ht ht1 => (congrArg norm (gaussianNoiseCLM_vectorChaos_sum ι b
      (by linarith) ht1 n f)).symm.trans_le (norm_gaussianNoiseL2_le ι t _)
  case horth =>
    exact fun i j hij => gaussianVectorChaos_inner_map_zero ι J b
      (fun h => hij (Fin.ext h)) f f
  case hE => exact norm_le_compLpL_of_bound (coordinateGaussian ι) J hE
  case hJ =>
    exact fun x => Lp.norm_le_norm_of_ae_le ((J.coeFn_compLpL x).mono
      (fun a ha => by simpa only [ha] using! hJ (x a)))

/-- The first Gaussian chaos projection has norm at most `3 √D` whenever the
specified norm is within distortion `D` of the comparison Hilbert norm. -/
theorem gaussianVectorChaos_first_norm_le (b : Basis κ ℝ E) (J : E →L[ℝ] H)
    {D : ℝ} (hD : 1 ≤ D) (hJ : ∀ x, ‖J x‖ ≤ ‖x‖) (hE : ∀ x, ‖x‖ ≤ D * ‖J x‖)
    (f : Lp E 2 (coordinateGaussian ι)) :
    ‖gaussianVectorChaos ι b 1 f‖ ≤ 3 * Real.sqrt D * ‖f‖ := by
  have h := (gaussianVectorChaos_sum_tendsto ι b f).comp (Filter.tendsto_add_atTop_nat 1)
  exact ge_of_tendsto' (h.norm.const_mul (3 * Real.sqrt D))
    (fun n => gaussianVectorChaos_first_norm_le_partial ι b J hD hJ hE n f)



variable (E) [FiniteDimensional ℝ E]

/-- The first Gaussian degree projection. Basis independence is proved above. -/
def gaussianFirstProjection :
    Lp E 2 (coordinateGaussian ι) →L[ℝ] Lp E 2 (coordinateGaussian ι) :=
  gaussianVectorChaos ι (Module.finBasis ℝ E) 1

variable {E}



end ConvexBodyChasing

end
end BundledModule075

/- Component source: ConvexBodyChasing.GaussianFirstChaos -/
section BundledModule076
/-! # The first Gaussian chaos as the span of the coordinate functions

This identifies the abstract degree-one orthogonal projection with the usual
Gaussian coefficient formula, using the actual means and covariances.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open MeasureTheory ProbabilityTheory Module
open scoped BigOperators
namespace ConvexBodyChasing

variable (ι : Type*) [Fintype ι]

omit [Fintype ι] in
theorem polynomial_degree_one_decomposition {P : MvPolynomial ι ℝ} (hP : P.totalDegree ≤ 1) :
    P = MvPolynomial.C (P.coeff 0) + MvPolynomial.homogeneousComponent 1 P := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hP with h0 | h1
  case inr =>
    simpa [h1, Finset.sum_range_succ, MvPolynomial.homogeneousComponent_zero] using!
      (MvPolynomial.sum_homogeneousComponent P).symm
  case inl =>
    simpa only [MvPolynomial.homogeneousComponent_eq_zero 1 P (show P.totalDegree < 1 by omega),
      add_zero] using! MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp h0

def gaussianCoordinateL2 (i : ι) : Lp ℝ 2 (coordinateGaussian ι) :=
  gaussianPolynomialL2 ι (MvPolynomial.X i)

theorem gaussianCoordinateL2_ae (i : ι) :
    gaussianCoordinateL2 ι i =ᵐ[coordinateGaussian ι] fun x => x i := by
  simpa only [gaussianCoordinateL2, MvPolynomial.eval_X] using!
    gaussianPolynomialL2_ae ι (MvPolynomial.X i)

theorem inner_gaussianCoordinateL2 (f : Lp ℝ 2 (coordinateGaussian ι)) (i : ι) :
    inner ℝ f (gaussianCoordinateL2 ι i) = ∫ x, f x * x i ∂coordinateGaussian ι := by
  simpa only [gaussianCoordinateL2, MvPolynomial.eval_X] using!
    inner_gaussianPolynomialL2 ι f (MvPolynomial.X i)

theorem gaussianCoordinateL2_inner [DecidableEq ι] (i j : ι) :
    inner ℝ (gaussianCoordinateL2 ι i) (gaussianCoordinateL2 ι j) = if i = j then 1 else 0 := by
  rw [inner_gaussianCoordinateL2]
  exact (integral_congr_ae ((gaussianCoordinateL2_ae ι i).mono
    (fun x hx => congrArg (fun z : ℝ => z * x j) hx))).trans (by
      simpa only [covariance, coordinateGaussian_mean, sub_zero] using!
        coordinateGaussian_covariance ι i j)

theorem gaussianCoordinateL2_inner_const (i : ι) (c : ℝ) :
    inner ℝ (gaussianCoordinateL2 ι i) (gaussianPolynomialL2 ι (MvPolynomial.C c)) = 0 := by
  rw [inner_gaussianPolynomialL2]
  simp only [MvPolynomial.eval_C, integral_mul_const,
    integral_congr_ae (gaussianCoordinateL2_ae ι i), coordinateGaussian_mean, zero_mul]

theorem exists_constant_of_mem_gaussianPolynomialSpace_zero
    {f : Lp ℝ 2 (coordinateGaussian ι)} (hf : f ∈ gaussianPolynomialSpace ι 0) :
    ∃ c : ℝ, gaussianPolynomialL2 ι (MvPolynomial.C c) = f := by
  obtain ⟨P, hP, rfl⟩ := (mem_gaussianPolynomialSpace_iff ι 0 f).mp hf
  exact ⟨P.coeff 0, congrArg (gaussianPolynomialL2 ι)
    (MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp (Nat.eq_zero_of_le_zero hP)).symm⟩

theorem gaussianCoordinateL2_mem_chaos (i : ι) :
    gaussianCoordinateL2 ι i ∈ gaussianChaosSpace ι 1 := by
  refine ⟨(mem_gaussianPolynomialSpace_iff ι 1 _).mpr
    ⟨MvPolynomial.X i, by simp, rfl⟩, ?_⟩
  rw [gaussianPolynomialSpaceLT_succ]
  intro g hg
  obtain ⟨c, rfl⟩ := exists_constant_of_mem_gaussianPolynomialSpace_zero ι hg
  exact (real_inner_comm (gaussianCoordinateL2 ι i) _).trans
    (gaussianCoordinateL2_inner_const ι i c)

def gaussianLinearSpace : Submodule ℝ (Lp ℝ 2 (coordinateGaussian ι)) :=
  Submodule.span ℝ (Set.range (gaussianCoordinateL2 ι))

theorem gaussianLinearSpace_le_chaos : gaussianLinearSpace ι ≤ gaussianChaosSpace ι 1 := by
  exact Submodule.span_le.mpr (fun _ ⟨i, hi⟩ => hi ▸ gaussianCoordinateL2_mem_chaos ι i)

theorem gaussian_homogeneous_one_mem_linear {P : MvPolynomial ι ℝ}
    (hP : P ∈ MvPolynomial.homogeneousSubmodule ι ℝ 1) :
    gaussianPolynomialL2 ι P ∈ gaussianLinearSpace ι := by
  have hspan : Submodule.span ℝ (Set.range (MvPolynomial.X : ι → MvPolynomial ι ℝ)) ≤
      (gaussianLinearSpace ι).comap (gaussianPolynomialEmbedding ι) :=
    Submodule.span_le.mpr (fun _ ⟨i, hi⟩ => hi ▸ Submodule.subset_span ⟨i, rfl⟩)
  exact hspan ((MvPolynomial.homogeneousSubmodule_one_eq_span_X (σ := ι) (R := ℝ)) ▸ hP)

theorem gaussianPolynomialSpace_one_le :
    gaussianPolynomialSpace ι 1 ≤ gaussianPolynomialSpace ι 0 ⊔ gaussianLinearSpace ι := by
  intro f hf
  obtain ⟨P, hP, rfl⟩ := (mem_gaussianPolynomialSpace_iff ι 1 f).mp hf
  rw [polynomial_degree_one_decomposition ι hP, gaussianPolynomialL2_add]
  exact Submodule.add_mem_sup
    ((mem_gaussianPolynomialSpace_iff ι 0 _).mpr ⟨MvPolynomial.C (P.coeff 0), by simp, rfl⟩)
    (gaussian_homogeneous_one_mem_linear ι (MvPolynomial.homogeneousComponent_mem 1 P))

theorem gaussianChaosSpace_one_eq_linear : gaussianChaosSpace ι 1 = gaussianLinearSpace ι := by
  apply le_antisymm _ (gaussianLinearSpace_le_chaos ι)
  intro f hf
  obtain ⟨g, hg, q, hq, hsum⟩ := Submodule.mem_sup.mp
    (gaussianPolynomialSpace_one_le ι hf.1)
  have horth (u : Lp ℝ 2 (coordinateGaussian ι)) (hu : u ∈ gaussianChaosSpace ι 1) :
      inner ℝ g u = 0 := Submodule.inner_right_of_mem_orthogonal
    (gaussianPolynomialSpace_le_LT ι (show 0 < 1 by decide) hg) hu.2
  have hg0 : g = 0 := (inner_self_eq_zero (𝕜 := ℝ)).mp (by
    simpa only [← hsum, inner_add_right, horth q (gaussianLinearSpace_le_chaos ι hq), add_zero]
      using! horth f hf)
  simpa only [← hsum, hg0, zero_add] using! hq

theorem inner_sum_gaussianCoordinateL2 (a : ι → ℝ) (j : ι) :
    inner ℝ (∑ i, a i • gaussianCoordinateL2 ι i) (gaussianCoordinateL2 ι j) = a j := by
  classical
  simp [sum_inner, real_inner_smul_left, gaussianCoordinateL2_inner]

/-- The scalar first-degree projection is the sum of the Gaussian coordinate coefficients. -/
theorem gaussianChaosProjection_one_eq_sum (f : Lp ℝ 2 (coordinateGaussian ι)) :
    gaussianChaosProjection ι 1 f =
      ∑ i, inner ℝ f (gaussianCoordinateL2 ι i) • gaussianCoordinateL2 ι i := by
  rw [gaussianChaosProjection]
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  case hvm =>
    exact (gaussianChaosSpace ι 1).sum_mem (fun i _ =>
      (gaussianChaosSpace ι 1).smul_mem _ (gaussianCoordinateL2_mem_chaos ι i))
  intro w hw
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp
    (gaussianChaosSpace_one_eq_linear ι ▸ hw)
  simp only [inner_sum, real_inner_smul_right, inner_sub_left,
    inner_sum_gaussianCoordinateL2, sub_self, Finset.sum_const_zero]

end ConvexBodyChasing

end
end BundledModule076

/- Component source: ConvexBodyChasing.DeterminantPosition -/
section BundledModule077
/-! # The determinant variational argument for Euclidean positions

These lemmas establish the finite-dimensional optimization step used in the
geometric QS argument. They do not assert the Gaussian or mean-width estimates
needed to finish that argument.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open Matrix Set Polynomial
open scoped Topology Matrix.Norms.Elementwise

namespace ConvexBodyChasing

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The first variation of the determinant at the identity. -/
theorem hasDerivAt_det_one_add_smul (A : Matrix ι ι ℝ) :
    HasDerivAt (fun t : ℝ => (1 + t • A).det) (Matrix.trace A) 0 := by
  have h := (Matrix.det (1 + (Polynomial.X : ℝ[X]) • A.map Polynomial.C)).hasDerivAt 0
  rw [Matrix.derivative_det_one_add_X_smul] at h
  convert! h using 1
  funext t
  rw [← Polynomial.coe_evalRingHom, RingHom.map_det]
  congr 1
  ext i j
  simp [Matrix.one_apply, apply_ite, Matrix.add_apply, Matrix.smul_apply]
  exact mul_comm _ _

private theorem deriv_nonpos_of_maxOn_unitInterval {f : ℝ → ℝ} {a : ℝ}
    (hmax : IsMaxOn f (Icc 0 1) 0) (hderiv : HasDerivAt f a 0) : a ≤ 0 := by
  have ht : (1 : ℝ) ∈ posTangentConeAt (Icc 0 1) 0 := by
    simpa using! sub_mem_posTangentConeAt_of_segment_subset
      (segment_subset_Icc (show (0 : ℝ) ≤ 1 by norm_num))
  simpa using! hmax.localize.hasFDerivWithinAt_nonpos
    hderiv.hasFDerivAt.hasFDerivWithinAt ht

/-- If the identity maximizes determinant on a convex matrix body, trace is a supporting
functional with value equal to the dimension. -/
theorem trace_le_card_of_det_max {K : Set (Matrix ι ι ℝ)} (hconvex : Convex ℝ K)
    (hI : (1 : Matrix ι ι ℝ) ∈ K) (hmax : IsMaxOn Matrix.det K 1)
    {A : Matrix ι ι ℝ} (hA : A ∈ K) : Matrix.trace A ≤ Fintype.card ι := by
  have hsegment (t : ℝ) (ht : t ∈ Icc 0 1) : 1 + t • (A - 1) ∈ K := by
    convert! hconvex hI hA (sub_nonneg.mpr ht.2) ht.1 (sub_add_cancel 1 t) using 1
    module
  have hcurve : IsMaxOn (fun t : ℝ => (1 + t • (A - 1)).det) (Icc 0 1) 0 := by
    exact fun t ht => by simpa using! hmax (hsegment t ht)
  simpa only [Matrix.trace_sub, Matrix.trace_one, sub_nonpos] using!
    deriv_nonpos_of_maxOn_unitInterval hcurve (hasDerivAt_det_one_add_smul (A - 1))

/-- Normalize a determinant maximizer to the identity to obtain the support inequality. -/
theorem trace_inv_mul_le_card_of_det_max {K : Set (Matrix ι ι ℝ)}
    (hconvex : Convex ℝ K) {T : Matrix ι ι ℝ} (hT : T ∈ K)
    (hdet : 0 < T.det) (hmax : IsMaxOn Matrix.det K T)
    {A : Matrix ι ι ℝ} (hA : A ∈ K) : Matrix.trace (T⁻¹ * A) ≤ Fintype.card ι := by
  let L := mulLeftLinearMap ι ℝ T⁻¹
  have hI : (1 : Matrix ι ι ℝ) ∈ L '' K :=
    ⟨T, hT, Matrix.nonsing_inv_mul T (isUnit_iff_ne_zero.mpr hdet.ne')⟩
  have hmaxI : IsMaxOn Matrix.det (L '' K) 1 := by
    rintro _ ⟨B, hB, rfl⟩
    simpa [L, Matrix.det_mul, Matrix.det_nonsing_inv, hdet.ne'] using!
      mul_le_mul_of_nonneg_left (hmax hB) (inv_nonneg.mpr hdet.le)
  exact trace_le_card_of_det_max (hconvex.linear_image L) hI hmaxI ⟨A, hA, rfl⟩

/-- Compactness produces a determinant position and its supporting trace functional. -/
theorem exists_determinant_position {K : Set (Matrix ι ι ℝ)} (hcompact : IsCompact K)
    (hconvex : Convex ℝ K) (hpositive : ∃ A ∈ K, 0 < Matrix.det A) :
    ∃ T ∈ K, 0 < Matrix.det T ∧ IsMaxOn Matrix.det K T ∧
      ∀ A ∈ K, Matrix.trace (T⁻¹ * A) ≤ Fintype.card ι := by
  obtain ⟨A, hA, hdetA⟩ := hpositive
  obtain ⟨T, hT, hmax⟩ := hcompact.exists_isMaxOn ⟨A, hA⟩
    continuous_id.matrix_det.continuousOn
  exact ⟨T, hT, hdetA.trans_le (hmax hA), hmax,
    fun B hB => trace_inv_mul_le_card_of_det_max hconvex hT
      (hdetA.trans_le (hmax hA)) hmax hB⟩

/-- Symmetry turns the supporting trace inequality into a norm bound. -/
theorem abs_trace_inv_mul_le_card_of_det_max {K : Set (Matrix ι ι ℝ)}
    (hconvex : Convex ℝ K) (hsymm : ∀ A ∈ K, -A ∈ K)
    {T : Matrix ι ι ℝ} (hT : T ∈ K) (hdet : 0 < T.det)
    (hmax : IsMaxOn Matrix.det K T) {A : Matrix ι ι ℝ} (hA : A ∈ K) :
    |Matrix.trace (T⁻¹ * A)| ≤ Fintype.card ι := by
  exact abs_le.mpr ⟨by
    simpa using! neg_le_neg
      (trace_inv_mul_le_card_of_det_max hconvex hT hdet hmax (hsymm A hA)),
    trace_inv_mul_le_card_of_det_max hconvex hT hdet hmax hA⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [DecidableEq ι] in
/-- Injectivity makes the unit ball of a pulled-back norm compact. -/
theorem isCompact_unitBall_preimage (J : Matrix ι ι ℝ →L[ℝ] E)
    (hinj : Function.Injective J) : IsCompact (J ⁻¹' Metric.closedBall 0 1) := by
  obtain ⟨C, _, hC⟩ := (LinearMap.injective_iff_antilipschitz
    (J : Matrix ι ι ℝ →ₗ[ℝ] E)).mp hinj
  exact Metric.isCompact_iff_isClosed_bounded.mpr
    ⟨Metric.isClosed_closedBall.preimage J.continuous,
      hC.isBounded_preimage Metric.isBounded_closedBall⟩

/-- A matrix norm unit ball contains a positive-determinant multiple of the identity. -/
theorem exists_positive_det_unitBall_preimage (J : Matrix ι ι ℝ →L[ℝ] E) :
    ∃ A ∈ J ⁻¹' Metric.closedBall 0 1, 0 < Matrix.det A := by
  have hc : 0 < (‖J 1‖ + 1)⁻¹ := inv_pos.mpr (by positivity)
  refine ⟨(‖J 1‖ + 1)⁻¹ • 1, ?_, by simpa using! pow_pos hc (Fintype.card ι)⟩
  simpa only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right, map_smul,
    norm_smul, Real.norm_of_nonneg hc.le, ← div_eq_inv_mul] using!
    (div_le_one (show 0 < ‖J 1‖ + 1 by positivity)).mpr (by linarith : ‖J 1‖ ≤ ‖J 1‖ + 1)

/-- The determinant position for any norm represented by a linear embedding. The resulting
trace functional has dual norm at most the matrix dimension. -/
theorem exists_norm_determinant_position (J : Matrix ι ι ℝ →L[ℝ] E)
    (hinj : Function.Injective J) :
    ∃ T : Matrix ι ι ℝ, ‖J T‖ ≤ 1 ∧ 0 < T.det ∧
      ∀ A : Matrix ι ι ℝ, |Matrix.trace (T⁻¹ * A)| ≤ (Fintype.card ι : ℝ) * ‖J A‖ := by
  have hconvex : Convex ℝ (J ⁻¹' Metric.closedBall 0 1) :=
    (convex_closedBall (0 : E) 1).linear_preimage J.toLinearMap
  obtain ⟨T, hT, hdet, hmax, _⟩ := exists_determinant_position
    (isCompact_unitBall_preimage J hinj) hconvex (exists_positive_det_unitBall_preimage J)
  refine ⟨T, by simpa using! hT, hdet, ?_⟩
  intro A
  by_cases hA : A = 0
  · simp [hA]
  · have hJA : 0 < ‖J A‖ := norm_pos_iff.mpr (fun hz => hA (hinj (hz.trans J.map_zero.symm)))
    have hunit : ‖J A‖⁻¹ • A ∈ J ⁻¹' Metric.closedBall 0 1 := by
      simp [norm_smul, hJA.ne']
    have hbound := abs_trace_inv_mul_le_card_of_det_max hconvex
      (fun B hB => by simpa using! hB) hT hdet hmax hunit
    simpa [Matrix.mul_smul, Matrix.trace_smul, abs_mul, abs_of_nonneg (norm_nonneg (J A)),
      hJA.ne'] using! (mul_le_mul_of_nonneg_left hbound hJA.le).trans_eq
        (mul_comm ‖J A‖ (Fintype.card ι : ℝ))

/-- In positive dimension the determinant position is normalized exactly to the unit sphere. -/
theorem exists_unit_norm_determinant_position [Nonempty ι]
    (J : Matrix ι ι ℝ →L[ℝ] E) (hinj : Function.Injective J) :
    ∃ T : Matrix ι ι ℝ, ‖J T‖ = 1 ∧ 0 < T.det ∧
      ∀ A : Matrix ι ι ℝ, |Matrix.trace (T⁻¹ * A)| ≤ (Fintype.card ι : ℝ) * ‖J A‖ := by
  obtain ⟨T, hT, hdet, hbound⟩ := exists_norm_determinant_position J hinj
  refine ⟨T, le_antisymm hT ?_, hdet, hbound⟩
  apply le_of_mul_le_mul_left (a := (Fintype.card ι : ℝ)) _
    (show (0 : ℝ) < Fintype.card ι by exact_mod_cast Fintype.card_pos)
  simpa [Matrix.nonsing_inv_mul T (isUnit_iff_ne_zero.mpr hdet.ne')] using! hbound T

end ConvexBodyChasing

end
end BundledModule077

/- Component source: ConvexBodyChasing.GaussianPosition -/
section BundledModule078
/-! # The Gaussian L² determinant position

The norm of a matrix is the actual L² norm of its Gaussian image in the given
normed space. Full support proves this matrix norm is nondegenerate. The
determinant-position theorem then supplies the variational trace estimate.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open MeasureTheory
open scoped NNReal ENNReal Matrix.Norms.Elementwise

namespace ConvexBodyChasing

variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Interpret a matrix as an operator from coordinate space into the normed space. -/
def matrixOperatorEquiv (b : Module.Basis ι ℝ E) :
    Matrix ι ι ℝ ≃ₗ[ℝ] ((ι → ℝ) →L[ℝ] E) :=
  (Matrix.toLin (Pi.basisFun ℝ ι) b).trans LinearMap.toContinuousLinearMap

/-- The Gaussian coordinate vector, regarded as an element of L². -/
def gaussianCoordinateVector : Lp (ι → ℝ) 2 (coordinateGaussian ι) :=
  (coordinateGaussian_memLp_id ι).toLp id

/-- Matrix evaluation in Gaussian L² is linear in the matrix. -/
def gaussianMatrixLinear (b : Module.Basis ι ℝ E) :
    Matrix ι ι ℝ →ₗ[ℝ] Lp E 2 (coordinateGaussian ι) where
  toFun A := (matrixOperatorEquiv b A).compLp gaussianCoordinateVector
  map_add' A B := by simp only [map_add, ContinuousLinearMap.add_compLp]
  map_smul' c A := by simp only [map_smul, ContinuousLinearMap.smul_compLp, RingHom.id_apply]

/-- Continuity follows because the matrix domain is finite dimensional. -/
def gaussianMatrixEmbedding (b : Module.Basis ι ℝ E) :
    Matrix ι ι ℝ →L[ℝ] Lp E 2 (coordinateGaussian ι) :=
  (gaussianMatrixLinear b).toContinuousLinearMap

/-- The L² representative agrees almost everywhere with the actual linear image. -/
theorem gaussianMatrixEmbedding_ae (b : Module.Basis ι ℝ E) (A : Matrix ι ι ℝ) :
    gaussianMatrixEmbedding b A =ᵐ[coordinateGaussian ι] fun x => matrixOperatorEquiv b A x := by
  exact Filter.EventuallyEq.trans
    ((matrixOperatorEquiv b A).coeFn_compLp gaussianCoordinateVector)
    ((coordinateGaussian_memLp_id ι).coeFn_toLp.fun_comp (matrixOperatorEquiv b A))

/-- Full support prevents two different linear maps from becoming equal in Gaussian L². -/
theorem gaussianMatrixEmbedding_injective (b : Module.Basis ι ℝ E) :
    Function.Injective (gaussianMatrixEmbedding b) := by
  intro A B hAB
  have hA := gaussianMatrixEmbedding_ae b A
  rw [hAB] at hA
  exact (matrixOperatorEquiv b).injective (DFunLike.coe_injective
    (Measure.eq_of_ae_eq (hA.symm.trans (gaussianMatrixEmbedding_ae b B))
      (matrixOperatorEquiv b A).continuous (matrixOperatorEquiv b B).continuous))

/-- The Gaussian matrix norm used in the determinant optimization. -/
def gaussianMatrixNorm (b : Module.Basis ι ℝ E) (A : Matrix ι ι ℝ) : ℝ :=
  ‖gaussianMatrixEmbedding b A‖

theorem gaussianMatrixNorm_eq_lpNorm (b : Module.Basis ι ℝ E) (A : Matrix ι ι ℝ) :
    gaussianMatrixNorm b A = lpNorm (fun x => matrixOperatorEquiv b A x) 2
      (coordinateGaussian ι) := by
  rw [gaussianMatrixNorm, Lp.norm_def, eLpNorm_congr_ae (gaussianMatrixEmbedding_ae b A)]
  exact toReal_eLpNorm
    ((matrixOperatorEquiv b A).comp_memLp' (coordinateGaussian_memLp_id ι)).aestronglyMeasurable



/-- The Gaussian determinant position exists for the actual norm of every finite-dimensional
real normed space, with its trace-duality estimate proved rather than assumed. -/
theorem exists_gaussian_determinant_position [Nonempty ι] (b : Module.Basis ι ℝ E) :
    ∃ T : Matrix ι ι ℝ, gaussianMatrixNorm b T = 1 ∧ 0 < T.det ∧
      ∀ A : Matrix ι ι ℝ,
        |Matrix.trace (T⁻¹ * A)| ≤ (Fintype.card ι : ℝ) * gaussianMatrixNorm b A :=
  exists_unit_norm_determinant_position (gaussianMatrixEmbedding b)
    (gaussianMatrixEmbedding_injective b)

end ConvexBodyChasing

end
end BundledModule078

/- Component source: ConvexBodyChasing.GaussianCoefficients -/
section BundledModule079
/-! # Gaussian coefficients of vector-valued L² functions

The coefficient integrals are integrable by Hölder. The first-chaos projection
is identified with the linear Gaussian image defined by these coefficients.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open MeasureTheory Module
open scoped BigOperators
namespace ConvexBodyChasing

variable (ι : Type*) [Fintype ι]
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def gaussianCoefficient (f : Lp E 2 (coordinateGaussian ι)) (i : ι) : E :=
  ∫ x, x i • f x ∂coordinateGaussian ι

theorem integrable_gaussianCoefficient (f : Lp E 2 (coordinateGaussian ι)) (i : ι) :
    Integrable (fun x : ι → ℝ => x i • f x) (coordinateGaussian ι) := by
  exact memLp_one_iff_integrable.mp
    ((Lp.memLp f).smul ((coordinateGaussian_memLp_id ι).eval i))

theorem map_gaussianCoefficient [CompleteSpace E] [CompleteSpace F] (L : E →L[ℝ] F)
    (f : Lp E 2 (coordinateGaussian ι)) (i : ι) :
    L (gaussianCoefficient ι f i) = gaussianCoefficient ι (L.compLpL 2 (coordinateGaussian ι) f) i := by
  rw [gaussianCoefficient, gaussianCoefficient, ← L.integral_comp_comm (integrable_gaussianCoefficient ι f i)]
  exact integral_congr_ae ((L.coeFn_compLpL f).mono
    (fun x hx => by simp only [hx, map_smul]))

theorem gaussianCoefficient_scalar (f : Lp ℝ 2 (coordinateGaussian ι)) (i : ι) :
    gaussianCoefficient ι f i = inner ℝ f (gaussianCoordinateL2 ι i) := by
  simp only [gaussianCoefficient, inner_gaussianCoordinateL2, smul_eq_mul, mul_comm]

theorem functional_gaussianCoefficient [CompleteSpace E] (L : E →L[ℝ] ℝ)
    (f : Lp E 2 (coordinateGaussian ι)) (i : ι) :
    L (gaussianCoefficient ι f i) =
      inner ℝ (L.compLpL 2 (coordinateGaussian ι) f) (gaussianCoordinateL2 ι i) :=
  (map_gaussianCoefficient ι L f i).trans (gaussianCoefficient_scalar ι _ i)

/-- The continuous linear map whose columns are the Gaussian coefficient vectors. -/
def gaussianCoefficientOperator (f : Lp E 2 (coordinateGaussian ι)) : (ι → ℝ) →L[ℝ] E :=
  ∑ i, (ContinuousLinearMap.toSpanSingleton ℝ (gaussianCoefficient ι f i)).comp
    (ContinuousLinearMap.proj i)

theorem gaussianCoefficientOperator_apply (f : Lp E 2 (coordinateGaussian ι)) (x : ι → ℝ) :
    gaussianCoefficientOperator ι f x = ∑ i, x i • gaussianCoefficient ι f i := by
  simp only [gaussianCoefficientOperator, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    ContinuousLinearMap.toSpanSingleton_apply]

variable [FiniteDimensional ℝ E]

/-- The vector-valued first Gaussian projection, in terms of actual Bochner integrals. -/
theorem gaussianFirstProjection_eq_sum (f : Lp E 2 (coordinateGaussian ι)) :
    gaussianFirstProjection ι E f =
      ∑ i, l2Vector (coordinateGaussian ι) (gaussianCoefficient ι f i) (gaussianCoordinateL2 ι i) := by
  apply l2_ext_functional (coordinateGaussian ι) (Module.finBasis ℝ E)
  exact fun L => by
    simp only [gaussianFirstProjection, gaussianVectorChaos, functional_l2Tensor,
      gaussianChaosProjection_one_eq_sum, map_sum, compLpL_l2Vector, l2Vector_scalar,
      functional_gaussianCoefficient]

theorem gaussianFirstProjection_ae (f : Lp E 2 (coordinateGaussian ι)) :
    gaussianFirstProjection ι E f =ᵐ[coordinateGaussian ι] gaussianCoefficientOperator ι f := by
  rw [gaussianFirstProjection_eq_sum]
  filter_upwards [l2_sum_ae (coordinateGaussian ι) Finset.univ
    (fun i => l2Vector (coordinateGaussian ι) (gaussianCoefficient ι f i) (gaussianCoordinateL2 ι i)),
    Filter.eventually_all.mpr (fun i => l2Vector_ae (coordinateGaussian ι)
      (gaussianCoefficient ι f i) (gaussianCoordinateL2 ι i)),
    Filter.eventually_all.mpr (fun i => gaussianCoordinateL2_ae ι i)] with x hs hv hg
  simp only [hs, hv, hg, gaussianCoefficientOperator_apply]

/-- The matrix with the Gaussian coefficient vectors as columns, in the given basis. -/
def gaussianCoefficientMatrix [DecidableEq ι] (b : Basis ι ℝ E)
    (f : Lp E 2 (coordinateGaussian ι)) : Matrix ι ι ℝ :=
  (matrixOperatorEquiv b).symm (gaussianCoefficientOperator ι f)

omit [FiniteDimensional ℝ E] in
@[simp] theorem matrixOperatorEquiv_coefficientMatrix [DecidableEq ι] (b : Basis ι ℝ E)
    (f : Lp E 2 (coordinateGaussian ι)) :
    matrixOperatorEquiv b (gaussianCoefficientMatrix ι b f) = gaussianCoefficientOperator ι f :=
  (matrixOperatorEquiv b).apply_symm_apply _

theorem gaussianMatrixEmbedding_coefficientMatrix [DecidableEq ι] (b : Basis ι ℝ E)
    (f : Lp E 2 (coordinateGaussian ι)) :
    gaussianMatrixEmbedding b (gaussianCoefficientMatrix ι b f) = gaussianFirstProjection ι E f := by
  apply Lp.ext
  refine Filter.EventuallyEq.trans ?_ (gaussianFirstProjection_ae ι f).symm
  simpa only [matrixOperatorEquiv_coefficientMatrix] using!
    gaussianMatrixEmbedding_ae b (gaussianCoefficientMatrix ι b f)

theorem gaussianMatrixNorm_coefficientMatrix_le [DecidableEq ι] (b : Basis ι ℝ E)
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (J : E →L[ℝ] H)
    {D : ℝ} (hD : 1 ≤ D) (hJ : ∀ x, ‖J x‖ ≤ ‖x‖) (hE : ∀ x, ‖x‖ ≤ D * ‖J x‖)
    (f : Lp E 2 (coordinateGaussian ι)) :
    gaussianMatrixNorm b (gaussianCoefficientMatrix ι b f) ≤ 3 * Real.sqrt D * ‖f‖ := by
  simpa only [gaussianMatrixNorm, gaussianMatrixEmbedding_coefficientMatrix, gaussianFirstProjection]
    using! gaussianVectorChaos_first_norm_le ι (Module.finBasis ℝ E) J hD hJ hE f

omit [FiniteDimensional ℝ E] in
theorem gaussianCoefficientOperator_single [DecidableEq ι]
    (f : Lp E 2 (coordinateGaussian ι)) (j : ι) :
    gaussianCoefficientOperator ι f (Pi.single j 1) = gaussianCoefficient ι f j := by
  simp [gaussianCoefficientOperator_apply, Pi.single_apply]

omit [FiniteDimensional ℝ E] in
theorem gaussianCoefficientMatrix_apply [DecidableEq ι] (b : Basis ι ℝ E)
    (f : Lp E 2 (coordinateGaussian ι)) (i j : ι) :
    gaussianCoefficientMatrix ι b f i j = b.equivFun (gaussianCoefficient ι f j) i := by
  simp only [gaussianCoefficientMatrix, matrixOperatorEquiv, LinearEquiv.symm_trans_apply,
    Matrix.toLin_symm, LinearMap.toMatrix_apply]
  simp only [LinearMap.coe_toContinuousLinearMap_symm, ContinuousLinearMap.coe_coe,
    Pi.basisFun_apply, gaussianCoefficientOperator_single]
  rw [Basis.equivFun_apply]

theorem exists_gaussian_position_coefficient_bound [DecidableEq ι] [Nonempty ι]
    (b : Basis ι ℝ E) {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (J : E →L[ℝ] H) {D : ℝ} (hD : 1 ≤ D)
    (hJ : ∀ x, ‖J x‖ ≤ ‖x‖) (hE : ∀ x, ‖x‖ ≤ D * ‖J x‖) :
    ∃ T : Matrix ι ι ℝ, gaussianMatrixNorm b T = 1 ∧ 0 < T.det ∧
      ∀ f : Lp E 2 (coordinateGaussian ι),
        |Matrix.trace (T⁻¹ * gaussianCoefficientMatrix ι b f)| ≤
          (Fintype.card ι : ℝ) * (3 * Real.sqrt D * ‖f‖) := by
  obtain ⟨T, hT, hd, ht⟩ := exists_gaussian_determinant_position b
  exact ⟨T, hT, hd, fun f => (ht _).trans (mul_le_mul_of_nonneg_left
    (gaussianMatrixNorm_coefficientMatrix_le ι b J hD hJ hE f) (Nat.cast_nonneg _))⟩

end ConvexBodyChasing

end
end BundledModule079

/- Component source: ConvexBodyChasing.GaussianTraceDuality -/
section BundledModule080
/-! # Gaussian trace pairings

A matrix trace against Gaussian coefficients is the actual integral pairing
with a dual-valued Gaussian linear image. All summands are integrable.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open MeasureTheory Module
open scoped BigOperators
namespace ConvexBodyChasing

variable (ι : Type*) [Fintype ι]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A linear Gaussian image specified by its column vectors. -/
def gaussianColumnOperator (v : ι → E) : (ι → ℝ) →L[ℝ] E :=
  ∑ i, (ContinuousLinearMap.toSpanSingleton ℝ (v i)).comp (ContinuousLinearMap.proj i)

theorem gaussianColumnOperator_apply (v : ι → E) (x : ι → ℝ) :
    gaussianColumnOperator ι v x = ∑ i, x i • v i := by
  simp only [gaussianColumnOperator, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    ContinuousLinearMap.toSpanSingleton_apply]

theorem gaussianColumnOperator_memLp (v : ι → E) :
    MemLp (gaussianColumnOperator ι v) 2 (coordinateGaussian ι) :=
  (gaussianColumnOperator ι v).comp_memLp' (coordinateGaussian_memLp_id ι)

theorem integrable_gaussian_functional_product (L : E →L[ℝ] ℝ)
    (f : Lp E 2 (coordinateGaussian ι)) (i : ι) :
    Integrable (fun x : ι → ℝ => x i * L (f x)) (coordinateGaussian ι) := by
  exact ((coordinateGaussian_memLp_id ι).eval i).integrable_mul (L.comp_memLp' (Lp.memLp f))

theorem integral_gaussian_functional_product [CompleteSpace E] (L : E →L[ℝ] ℝ)
    (f : Lp E 2 (coordinateGaussian ι)) (i : ι) :
    ∫ x, x i * L (f x) ∂coordinateGaussian ι = L (gaussianCoefficient ι f i) := by
  simpa only [gaussianCoefficient, map_smul, smul_eq_mul] using!
    L.integral_comp_comm (integrable_gaussianCoefficient ι f i)

theorem gaussian_dual_pairing_integral [CompleteSpace E] (L : ι → E →L[ℝ] ℝ)
    (f : Lp E 2 (coordinateGaussian ι)) :
    ∫ x, (gaussianColumnOperator ι L x) (f x) ∂coordinateGaussian ι =
      ∑ i, L i (gaussianCoefficient ι f i) := by
  simp only [gaussianColumnOperator_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  exact (integral_finset_sum Finset.univ
    (fun i _ => integrable_gaussian_functional_product ι (L i) f i)).trans
      (Finset.sum_congr rfl (fun i _ => integral_gaussian_functional_product ι (L i) f i))



/-- The row of a matrix, interpreted as a continuous linear functional through the basis. -/
def matrixRowFunctional (b : Basis ι ℝ E) (B : Matrix ι ι ℝ) (i : ι) : E →L[ℝ] ℝ :=
  ∑ j, B i j • ((ContinuousLinearMap.proj j).comp b.equivFunL.toContinuousLinearMap)

theorem matrixRowFunctional_apply (b : Basis ι ℝ E) (B : Matrix ι ι ℝ) (i : ι) (x : E) :
    matrixRowFunctional ι b B i x = ∑ j, B i j * b.equivFun x j := by
  simp only [matrixRowFunctional, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    ContinuousLinearEquiv.coe_coe, Basis.equivFunL_apply, Basis.equivFun_apply, smul_eq_mul]

theorem trace_mul_gaussianCoefficientMatrix [DecidableEq ι] (b : Basis ι ℝ E)
    (B : Matrix ι ι ℝ) (f : Lp E 2 (coordinateGaussian ι)) :
    Matrix.trace (B * gaussianCoefficientMatrix ι b f) =
      ∑ i, matrixRowFunctional ι b B i (gaussianCoefficient ι f i) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, gaussianCoefficientMatrix_apply,
    matrixRowFunctional_apply]

theorem trace_mul_gaussianCoefficientMatrix_eq_integral [DecidableEq ι] [CompleteSpace E]
    (b : Basis ι ℝ E) (B : Matrix ι ι ℝ) (f : Lp E 2 (coordinateGaussian ι)) :
    Matrix.trace (B * gaussianCoefficientMatrix ι b f) =
      ∫ x, (gaussianColumnOperator ι (matrixRowFunctional ι b B) x) (f x) ∂coordinateGaussian ι :=
  (trace_mul_gaussianCoefficientMatrix ι b B f).trans
    (gaussian_dual_pairing_integral ι (matrixRowFunctional ι b B) f).symm

/-- The determinant position controls the dual Gaussian pairing on every vector-valued L² input. -/
theorem exists_gaussian_position_pairing_bound [DecidableEq ι] [Nonempty ι]
    [FiniteDimensional ℝ E] (b : Basis ι ℝ E)
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (J : E →L[ℝ] H) {D : ℝ} (hD : 1 ≤ D)
    (hJ : ∀ x, ‖J x‖ ≤ ‖x‖) (hE : ∀ x, ‖x‖ ≤ D * ‖J x‖) :
    ∃ T : Matrix ι ι ℝ, gaussianMatrixNorm b T = 1 ∧ 0 < T.det ∧
      ∀ f : Lp E 2 (coordinateGaussian ι),
        |∫ x, (gaussianColumnOperator ι (matrixRowFunctional ι b T⁻¹) x) (f x)
          ∂coordinateGaussian ι| ≤ (Fintype.card ι : ℝ) * (3 * Real.sqrt D * ‖f‖) := by
  obtain ⟨T, hT, hd, ht⟩ := exists_gaussian_position_coefficient_bound ι b J hD hJ hE
  exact ⟨T, hT, hd, fun f => by
    simpa only [trace_mul_gaussianCoefficientMatrix_eq_integral] using! ht f⟩

end ConvexBodyChasing

end
end BundledModule080

/- Component source: ConvexBodyChasing.DualNorming -/
section BundledModule081
/-! # Measurable approximate norming vectors for a real finite-dimensional dual

A fixed countable dense subset of the unit ball allows a measurable first-index
selection. It loses only a universal factor two, independently of dimension.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open MeasureTheory Metric
namespace ConvexBodyChasing

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_unitBall_eval_gt_half (L : E →L[ℝ] ℝ) (hL : L ≠ 0) :
    ∃ x : E, ‖x‖ ≤ 1 ∧ ‖L‖ / 2 < L x := by
  have hlt : ‖L‖ / 2 < sSup ((fun x : E => ‖L x‖) '' closedBall 0 1) := by
    rw [L.sSup_unitClosedBall_eq_norm]
    exact half_lt_self (norm_pos_iff.mpr hL)
  obtain ⟨_, ⟨x, hx, rfl⟩, hr⟩ := exists_lt_of_lt_csSup
    ((nonempty_closedBall.mpr (show (0 : ℝ) ≤ 1 by norm_num)).image (fun x : E => ‖L x‖)) hlt
  rcases lt_abs.mp hr with hp | hn
  case inr => exact ⟨-x, by simpa only [mem_closedBall_zero_iff, norm_neg] using! hx,
    by simpa only [map_neg] using! hn⟩
  case inl => exact ⟨x, mem_closedBall_zero_iff.mp hx, hp⟩

variable (E) [FiniteDimensional ℝ E]

local instance unitNormingBall_nonempty : Nonempty {x : E // ‖x‖ ≤ 1} := ⟨⟨0, by simp⟩⟩

/-- A fixed countable dense family in the closed unit ball. -/
def unitNormingSeq : ℕ → {x : E // ‖x‖ ≤ 1} :=
  TopologicalSpace.denseSeq {x : E // ‖x‖ ≤ 1}

theorem exists_unitNormingSeq_eval (L : E →L[ℝ] ℝ) :
    ∃ n : ℕ, ‖L‖ / 2 ≤ L (unitNormingSeq E n) := by
  by_cases hL : L = 0
  · exact ⟨0, by simp [hL]⟩
  obtain ⟨x, hx, hr⟩ := exists_unitBall_eval_gt_half L hL
  obtain ⟨n, hn⟩ := (TopologicalSpace.denseRange_denseSeq {x : E // ‖x‖ ≤ 1}).exists_mem_open
    (isOpen_lt continuous_const (L.continuous.comp continuous_subtype_val)) ⟨⟨x, hx⟩, hr⟩
  exact ⟨n, hn.le⟩

/-- A measurable choice of unit-ball vectors that norm every functional within factor two. -/
theorem exists_stronglyMeasurable_norming {Ω : Type*} [MeasurableSpace Ω]
    (g : Ω → E →L[ℝ] ℝ) (hg : StronglyMeasurable g) :
    ∃ v : Ω → E, StronglyMeasurable v ∧ (∀ x, ‖v x‖ ≤ 1) ∧
      ∀ x, ‖g x‖ / 2 ≤ g x (v x) := by
  have hp (x : Ω) : ∃ n : ℕ, ‖g x‖ / 2 ≤ g x (unitNormingSeq E n) :=
    exists_unitNormingSeq_eval E (g x)
  have hm : Measurable (fun x => Nat.find (hp x)) := measurable_find hp (fun n =>
    measurableSet_le (hg.norm.measurable.div_const 2)
      ((show Continuous (fun L : E →L[ℝ] ℝ => L (unitNormingSeq E n)) from by fun_prop).comp_stronglyMeasurable hg).measurable)
  refine ⟨fun x => (unitNormingSeq E (Nat.find (hp x))).val, ?_,
    fun x => (unitNormingSeq E (Nat.find (hp x))).property, fun x => Nat.find_spec (hp x)⟩
  exact (StronglyMeasurable.of_discrete (f := fun n : ℕ => (unitNormingSeq E n).val)).comp_measurable hm

end ConvexBodyChasing

end
end BundledModule081

/- Component source: ConvexBodyChasing.L2DualEstimate -/
section BundledModule082
/-! # Recovering a dual-valued L² norm from integral pairings

Measurable approximate norming vectors give a factor-two estimate. No
representation theorem for the dual of a Bochner space is assumed.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open MeasureTheory
namespace ConvexBodyChasing

variable {Ω E : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem integrable_l2_dual_pairing {g : Ω → E →L[ℝ] ℝ} {f : Ω → E}
    (hg : MemLp g 2 μ) (hf : MemLp f 2 μ) : Integrable (fun x => g x (f x)) μ := by
  exact memLp_one_iff_integrable.mp
    ((ContinuousLinearMap.apply ℝ ℝ).flip.memLp_of_bilin 1 hg hf)

theorem norm_toLp_two_sq {F : Type*} [NormedAddCommGroup F] {g : Ω → F} (hg : MemLp g 2 μ) :
    ‖hg.toLp g‖ ^ 2 = ∫ x, ‖g x‖ ^ 2 ∂μ := by
  rw [norm_Lp_two_eq_sqrt_integral, Real.sq_sqrt (integral_nonneg (fun _ => sq_nonneg _))]
  exact integral_congr_ae (hg.coeFn_toLp.mono (fun x hx => congrArg (fun z => ‖z‖ ^ 2) hx))

/-- Integral pairing bounds recover the L² norm of a dual-valued function within factor two. -/
theorem norm_L2_dual_le_of_pairing (g : Ω → E →L[ℝ] ℝ)
    (hgm : StronglyMeasurable g) (hg : MemLp g 2 μ) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ f : Lp E 2 μ, |∫ x, g x (f x) ∂μ| ≤ C * ‖f‖) :
    ‖hg.toLp g‖ ≤ 2 * C := by
  obtain ⟨v, hv, hvnorm, hveval⟩ := exists_stronglyMeasurable_norming E g hgm
  have hnorm (x : Ω) : ‖‖g x‖ • v x‖ ≤ ‖g x‖ := by
    simpa only [norm_smul, norm_norm, mul_one] using!
      mul_le_mul_of_nonneg_left (hvnorm x) (norm_nonneg (g x))
  have hf : MemLp (fun x => ‖g x‖ • v x) 2 μ :=
    hg.of_le (hgm.norm.smul hv).aestronglyMeasurable (Filter.Eventually.of_forall hnorm)
  let f : Lp E 2 μ := hf.toLp (fun x => ‖g x‖ • v x)
  have hfnorm : ‖f‖ ≤ ‖hg.toLp g‖ := Lp.norm_le_norm_of_ae_le
    ((hf.coeFn_toLp.and hg.coeFn_toLp).mono
      (fun x hx => by simpa only [f, hx.1, hx.2] using! hnorm x))
  have hpoint : ∀ᵐ x ∂μ, ‖g x‖ ^ 2 / 2 ≤ g x (f x) := hf.coeFn_toLp.mono
    (fun x hx => by
      simpa only [f, hx, map_smul, smul_eq_mul, pow_two, div_eq_mul_inv, mul_assoc] using!
        mul_le_mul_of_nonneg_left (hveval x) (norm_nonneg (g x)))
  have hlower := integral_mono_ae (hg.norm.integrable_sq.div_const 2)
    (integrable_l2_dual_pairing μ hg (Lp.memLp f)) hpoint
  rw [integral_div, ← norm_toLp_two_sq μ hg] at hlower
  have hupper : ∫ x, g x (f x) ∂μ ≤ C * ‖hg.toLp g‖ :=
    (le_abs_self _).trans ((hbound f).trans (mul_le_mul_of_nonneg_left hfnorm hC))
  rcases (norm_nonneg (hg.toLp g)).eq_or_lt with hz | hpos
  case inr => exact le_of_mul_le_mul_left (a := ‖hg.toLp g‖) (by nlinarith [hlower.trans hupper]) hpos
  case inl => linarith

end ConvexBodyChasing

end
end BundledModule082

/- Component source: ConvexBodyChasing.GaussianMMStar -/
section BundledModule083
/-! # A Gaussian MM* position with sublinear distortion dependence

The determinant position and the actual first-chaos estimate give the dual
Gaussian L² norm bound. Measurable norming vectors justify the duality step.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open MeasureTheory Module
open scoped BigOperators
namespace ConvexBodyChasing

variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Coordinates of the primal matrix image in the given basis. -/
theorem equivFun_matrixOperatorEquiv (b : Basis ι ℝ E) (T : Matrix ι ι ℝ)
    (y : ι → ℝ) : b.equivFun (matrixOperatorEquiv b T y) = T.mulVec y := by
  change b.repr (Matrix.toLin (Pi.basisFun ℝ ι) b T y) = T.mulVec y
  rw [Matrix.repr_toLin]
  exact congrArg T.mulVec (funext (Pi.basisFun_repr ℝ ι y))

/-- Matrix rows evaluate on the primal image by matrix multiplication. -/
theorem matrixRowFunctional_matrixOperatorEquiv (b : Basis ι ℝ E)
    (B T : Matrix ι ι ℝ) (i : ι) (y : ι → ℝ) :
    matrixRowFunctional ι b B i (matrixOperatorEquiv b T y) = (B * T).mulVec y i := by
  rw [matrixRowFunctional_apply, equivFun_matrixOperatorEquiv]
  exact congrFun (Matrix.mulVec_mulVec y B T) i



/-- Gaussian L² norm of the dual linear image formed by the rows of a matrix. -/
def gaussianRowDualNorm (b : Basis ι ℝ E) (B : Matrix ι ι ℝ) : ℝ :=
  ‖(gaussianColumnOperator_memLp ι (matrixRowFunctional ι b B)).toLp
    (gaussianColumnOperator ι (matrixRowFunctional ι b B))‖



/-- A normalized Gaussian MM* position, with product bound `6 n √D`. -/
theorem exists_gaussian_MMstar_position [Nonempty ι] [FiniteDimensional ℝ E]
    (b : Basis ι ℝ E) {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (J : E →L[ℝ] H) {D : ℝ} (hD : 1 ≤ D)
    (hJ : ∀ x, ‖J x‖ ≤ ‖x‖) (hE : ∀ x, ‖x‖ ≤ D * ‖J x‖) :
    ∃ T : Matrix ι ι ℝ, gaussianMatrixNorm b T = 1 ∧ 0 < T.det ∧
      gaussianRowDualNorm b T⁻¹ ≤ 6 * (Fintype.card ι : ℝ) * Real.sqrt D := by
  obtain ⟨T, hT, hd, ht⟩ := exists_gaussian_position_pairing_bound ι b J hD hJ hE
  have hb : gaussianRowDualNorm b T⁻¹ ≤ 2 * ((Fintype.card ι : ℝ) * (3 * Real.sqrt D)) :=
    norm_L2_dual_le_of_pairing (coordinateGaussian ι)
      (gaussianColumnOperator ι (matrixRowFunctional ι b T⁻¹))
      (gaussianColumnOperator ι (matrixRowFunctional ι b T⁻¹)).continuous.stronglyMeasurable
      (gaussianColumnOperator_memLp ι (matrixRowFunctional ι b T⁻¹)) (by positivity)
      (fun f => by simpa only [mul_assoc] using! ht f)
  exact ⟨T, hT, hd, hb.trans_eq (by ring)⟩

end ConvexBodyChasing

end
end BundledModule083

/- Component source: ConvexBodyChasing.LogSumExp -/
section BundledModule084
/-! # Log-sum-exp and its bounded derivatives

Positive normalized exponential weights give the first and second derivatives
needed for Gaussian min–max smoothing.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators
namespace ConvexBodyChasing

variable {ι : Type*} [Fintype ι] [Nonempty ι]

def expSum (x : ι → ℝ) : ℝ := ∑ i, Real.exp (x i)

def softmaxWeight (x : ι → ℝ) (i : ι) : ℝ := Real.exp (x i) / expSum x

def logSumExp (x : ι → ℝ) : ℝ := Real.log (expSum x)

def logSumExpGradient (x : ι → ℝ) : (ι → ℝ) →L[ℝ] ℝ :=
  ∑ i, softmaxWeight x i • ContinuousLinearMap.proj i

def softmaxDerivative (x : ι → ℝ) (i : ι) : (ι → ℝ) →L[ℝ] ℝ :=
  softmaxWeight x i • (ContinuousLinearMap.proj i - logSumExpGradient x)

def logSumExpHessian (x : ι → ℝ) : (ι → ℝ) →L[ℝ] (ι → ℝ) →L[ℝ] ℝ :=
  ∑ i, (softmaxDerivative x i).smulRight (ContinuousLinearMap.proj i)

theorem expSum_pos (x : ι → ℝ) : 0 < expSum x := by
  exact Finset.sum_pos (fun i _ => Real.exp_pos (x i)) Finset.univ_nonempty

theorem softmaxWeight_pos (x : ι → ℝ) (i : ι) : 0 < softmaxWeight x i :=
  div_pos (Real.exp_pos _) (expSum_pos x)

theorem sum_softmaxWeight (x : ι → ℝ) : ∑ i, softmaxWeight x i = 1 := by
  simpa only [softmaxWeight, ← Finset.sum_div, expSum] using! div_self (expSum_pos x).ne'



omit [Nonempty ι] in
theorem hasFDerivAt_expSum (x : ι → ℝ) :
    HasFDerivAt expSum
      (∑ i, Real.exp (x i) • (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ)) x := by
  exact HasFDerivAt.fun_sum (fun i _ =>
    (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).hasFDerivAt.exp)

theorem hasFDerivAt_logSumExp (x : ι → ℝ) :
    HasFDerivAt logSumExp (logSumExpGradient x) x := by
  simpa only [logSumExp, logSumExpGradient, softmaxWeight, Finset.smul_sum,
    smul_smul, div_eq_mul_inv, mul_comm] using!
      (hasFDerivAt_expSum x).log (expSum_pos x).ne'

theorem softmaxWeight_eq_exp_sub (x : ι → ℝ) (i : ι) :
    softmaxWeight x i = Real.exp (x i - logSumExp x) := by
  simp only [softmaxWeight, logSumExp, Real.exp_sub, Real.exp_log (expSum_pos x)]

theorem hasFDerivAt_softmaxWeight (x : ι → ℝ) (i : ι) :
    HasFDerivAt (fun y => softmaxWeight y i) (softmaxDerivative x i) x := by
  simpa only [softmaxWeight_eq_exp_sub, softmaxDerivative] using!
    ((ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).hasFDerivAt.sub
      (hasFDerivAt_logSumExp x)).exp

theorem hasFDerivAt_logSumExpGradient (x : ι → ℝ) :
    HasFDerivAt logSumExpGradient (logSumExpHessian x) x := by
  exact HasFDerivAt.fun_sum (fun i _ =>
    (hasFDerivAt_softmaxWeight x i).smul_const
      (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ))

theorem continuous_softmaxWeight (i : ι) : Continuous (fun x : ι → ℝ => softmaxWeight x i) :=
  continuous_iff_continuousAt.mpr (fun x => (hasFDerivAt_softmaxWeight x i).continuousAt)

theorem continuous_logSumExpGradient : Continuous (logSumExpGradient (ι := ι)) :=
  continuous_iff_continuousAt.mpr (fun x => (hasFDerivAt_logSumExpGradient x).continuousAt)

theorem continuous_softmaxDerivative (i : ι) :
    Continuous (fun x : ι → ℝ => softmaxDerivative x i) := by
  exact (continuous_softmaxWeight i).smul
    (continuous_const.sub continuous_logSumExpGradient)

theorem continuous_logSumExpHessian : Continuous (logSumExpHessian (ι := ι)) := by
  letI : ContinuousAdd ((ι → ℝ) →L[ℝ] (ι → ℝ) →L[ℝ] ℝ) :=
    (inferInstance : IsTopologicalAddGroup ((ι → ℝ) →L[ℝ] (ι → ℝ) →L[ℝ] ℝ)).toContinuousAdd
  exact continuous_finset_sum _ (fun i _ =>
    ((ContinuousLinearMap.smulRightL ℝ (ι → ℝ) ((ι → ℝ) →L[ℝ] ℝ)).continuous.comp
      (continuous_softmaxDerivative i)).clm_apply continuous_const)

omit [Nonempty ι] in
theorem norm_coordinateProjection_le (i : ι) :
    ‖(ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ)‖ ≤ 1 := by
  exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    (fun v => by simpa only [ContinuousLinearMap.proj_apply, one_mul] using! norm_le_pi_norm v i)

theorem norm_logSumExpGradient_le (x : ι → ℝ) : ‖logSumExpGradient x‖ ≤ 1 := by
  calc
    ‖logSumExpGradient x‖ ≤ ∑ i, ‖softmaxWeight x i •
        (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ)‖ := norm_sum_le _ _
    _ ≤ ∑ i, softmaxWeight x i := Finset.sum_le_sum (fun i _ => by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (softmaxWeight_pos x i)]
      exact mul_le_of_le_one_right (softmaxWeight_pos x i).le (norm_coordinateProjection_le i))
    _ = 1 := sum_softmaxWeight x

theorem norm_softmaxDerivative_le (x : ι → ℝ) (i : ι) :
    ‖softmaxDerivative x i‖ ≤ softmaxWeight x i * 2 := by
  rw [softmaxDerivative, norm_smul, Real.norm_eq_abs, abs_of_pos (softmaxWeight_pos x i)]
  apply mul_le_mul_of_nonneg_left _ (softmaxWeight_pos x i).le
  exact (norm_sub_le _ _).trans (by
    linarith [norm_coordinateProjection_le (ι := ι) i, norm_logSumExpGradient_le x])

theorem norm_logSumExpHessian_le (x : ι → ℝ) : ‖logSumExpHessian x‖ ≤ 2 := by
  calc
    ‖logSumExpHessian x‖ ≤ ∑ i, ‖(softmaxDerivative x i).smulRight
        (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ)‖ :=
      norm_sum_le Finset.univ (fun i => (softmaxDerivative x i).smulRight
        (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ))
    _ ≤ ∑ i, softmaxWeight x i * 2 := Finset.sum_le_sum (fun i _ => by
      rw [ContinuousLinearMap.norm_smulRight_apply]
      exact (mul_le_of_le_one_right (norm_nonneg _) (norm_coordinateProjection_le i)).trans
        (norm_softmaxDerivative_le x i))
    _ = 2 := by rw [← Finset.sum_mul, sum_softmaxWeight, one_mul]

omit [Nonempty ι] in
theorem logSumExpGradient_single [DecidableEq ι] (x : ι → ℝ) (i : ι) :
    logSumExpGradient x (Pi.single i 1) = softmaxWeight x i := by
  simp [logSumExpGradient, Pi.single_apply]



theorem coordinate_le_logSumExp (x : ι → ℝ) (i : ι) : x i ≤ logSumExp x := by
  apply (Real.le_log_iff_exp_le (expSum_pos x)).mpr
  exact Finset.single_le_sum (fun j _ => (Real.exp_pos (x j)).le) (Finset.mem_univ i)

theorem logSumExp_le_of_coordinate_le (x : ι → ℝ) (M : ℝ) (hM : ∀ i, x i ≤ M) :
    logSumExp x ≤ M + Real.log (Fintype.card ι) := by
  apply (Real.log_le_iff_le_exp (expSum_pos x)).mpr
  rw [Real.exp_add, Real.exp_log (Nat.cast_pos.mpr Fintype.card_pos)]
  exact (Finset.sum_le_sum (fun i _ => Real.exp_le_exp.mpr (hM i))).trans_eq (by
    simp [mul_comm])

end ConvexBodyChasing

end
end BundledModule084

/- Component source: ConvexBodyChasing.SmoothMinMax -/
section BundledModule085
/-! # Smooth finite min–max

The negative log-sum-exp of negative row log-sum-exp values is a smooth
approximation to the minimum of the row maxima.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators
namespace ConvexBodyChasing

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty ι] [Nonempty κ]

def minMaxRow (i : ι) : ((ι × κ) → ℝ) →L[ℝ] (κ → ℝ) :=
  ContinuousLinearMap.pi (fun j => ContinuousLinearMap.proj (i, j))

def minMaxRowValues (x : (ι × κ) → ℝ) (i : ι) : ℝ := logSumExp (minMaxRow i x)

def minMaxRowGradient (x : (ι × κ) → ℝ) (i : ι) : ((ι × κ) → ℝ) →L[ℝ] ℝ :=
  (logSumExpGradient (minMaxRow i x)).comp (minMaxRow i)

def minMaxRowsDerivative (x : (ι × κ) → ℝ) : ((ι × κ) → ℝ) →L[ℝ] (ι → ℝ) :=
  ContinuousLinearMap.pi (minMaxRowGradient x)

def minMaxRowHessian (x : (ι × κ) → ℝ) (i : ι) :
    ((ι × κ) → ℝ) →L[ℝ] ((ι × κ) → ℝ) →L[ℝ] ℝ :=
  ((ContinuousLinearMap.compL ℝ ((ι × κ) → ℝ) (κ → ℝ) ℝ).flip (minMaxRow i)).comp
    ((logSumExpHessian (minMaxRow i x)).comp (minMaxRow i))

def minMaxRowWeight (x : (ι × κ) → ℝ) (i : ι) : ℝ :=
  softmaxWeight (-minMaxRowValues x) i

def smoothMinMax (x : (ι × κ) → ℝ) : ℝ := -logSumExp (-minMaxRowValues x)

def smoothMinMaxGradient (x : (ι × κ) → ℝ) : ((ι × κ) → ℝ) →L[ℝ] ℝ :=
  ∑ i, minMaxRowWeight x i • minMaxRowGradient x i

def minMaxRowWeightDerivative (x : (ι × κ) → ℝ) (i : ι) : ((ι × κ) → ℝ) →L[ℝ] ℝ :=
  minMaxRowWeight x i • (smoothMinMaxGradient x - minMaxRowGradient x i)

def smoothMinMaxHessian (x : (ι × κ) → ℝ) :
    ((ι × κ) → ℝ) →L[ℝ] ((ι × κ) → ℝ) →L[ℝ] ℝ :=
  ∑ i, ((minMaxRowWeightDerivative x i).smulRight (minMaxRowGradient x i) +
    minMaxRowWeight x i • minMaxRowHessian x i)

omit [Nonempty ι] in
theorem hasFDerivAt_minMaxRowValues (x : (ι × κ) → ℝ) (i : ι) :
    HasFDerivAt (fun y => minMaxRowValues y i) (minMaxRowGradient x i) x := by
  exact (hasFDerivAt_logSumExp (minMaxRow i x)).comp x (minMaxRow i).hasFDerivAt

omit [Nonempty ι] in
theorem hasFDerivAt_minMaxRowGradient (x : (ι × κ) → ℝ) (i : ι) :
    HasFDerivAt (fun y => minMaxRowGradient y i) (minMaxRowHessian x i) x := by
  exact ((ContinuousLinearMap.compL ℝ ((ι × κ) → ℝ) (κ → ℝ) ℝ).flip
    (minMaxRow i)).hasFDerivAt.comp x
      ((hasFDerivAt_logSumExpGradient (minMaxRow i x)).comp x (minMaxRow i).hasFDerivAt)

omit [Nonempty ι] in
theorem hasFDerivAt_minMaxRows (x : (ι × κ) → ℝ) :
    HasFDerivAt minMaxRowValues (minMaxRowsDerivative x) x := by
  exact hasFDerivAt_pi.mpr (hasFDerivAt_minMaxRowValues x)

omit [Nonempty ι] [Nonempty κ] in
theorem smoothMinMaxGradient_eq_comp (x : (ι × κ) → ℝ) :
    smoothMinMaxGradient x =
      (logSumExpGradient (-minMaxRowValues x)).comp (minMaxRowsDerivative x) := by
  ext v
  simp [smoothMinMaxGradient, logSumExpGradient, minMaxRowsDerivative, minMaxRowWeight]

theorem hasFDerivAt_smoothMinMax (x : (ι × κ) → ℝ) :
    HasFDerivAt smoothMinMax (smoothMinMaxGradient x) x := by
  simpa only [smoothMinMax, smoothMinMaxGradient_eq_comp, ContinuousLinearMap.comp_neg,
    neg_neg] using! ((hasFDerivAt_logSumExp (-minMaxRowValues x)).comp x
      (hasFDerivAt_minMaxRows x).neg).neg

theorem hasFDerivAt_minMaxRowWeight (x : (ι × κ) → ℝ) (i : ι) :
    HasFDerivAt (fun y => minMaxRowWeight y i) (minMaxRowWeightDerivative x i) x := by
  convert! (hasFDerivAt_softmaxWeight (-minMaxRowValues x) i).comp x
    (hasFDerivAt_minMaxRows x).neg using 1
  ext v
  simp [minMaxRowWeightDerivative, minMaxRowWeight, softmaxDerivative,
    smoothMinMaxGradient_eq_comp, minMaxRowsDerivative, mul_sub]

theorem hasFDerivAt_smoothMinMaxGradient (x : (ι × κ) → ℝ) :
    HasFDerivAt smoothMinMaxGradient (smoothMinMaxHessian x) x := by
  simpa only [smoothMinMaxGradient, smoothMinMaxHessian, add_comm] using!
    HasFDerivAt.fun_sum (fun i _ =>
      (hasFDerivAt_minMaxRowWeight x i).smul (hasFDerivAt_minMaxRowGradient x i))

omit [Fintype ι] [Fintype κ] [Nonempty ι] [Nonempty κ] in
theorem minMaxRow_single [DecidableEq ι] [DecidableEq κ] (i j : ι) (k : κ) :
    minMaxRow i (Pi.single (j, k) 1) = if i = j then Pi.single k 1 else 0 := by
  ext l
  by_cases h : i = j <;> simp [minMaxRow, Pi.single_apply, h, eq_comm]

omit [Fintype ι] [Nonempty ι] [Nonempty κ] in
theorem minMaxRowGradient_single [DecidableEq ι] [DecidableEq κ]
    (x : (ι × κ) → ℝ) (i j : ι) (k : κ) :
    minMaxRowGradient x i (Pi.single (j, k) 1) =
      if i = j then softmaxWeight (minMaxRow i x) k else 0 := by
  simp only [minMaxRowGradient, ContinuousLinearMap.comp_apply, minMaxRow_single]
  split_ifs <;> simp [logSumExpGradient_single]

omit [Nonempty ι] [Nonempty κ] in
theorem smoothMinMaxGradient_single [DecidableEq ι] [DecidableEq κ]
    (x : (ι × κ) → ℝ) (j : ι) (k : κ) :
    smoothMinMaxGradient x (Pi.single (j, k) 1) =
      minMaxRowWeight x j * softmaxWeight (minMaxRow j x) k := by
  simp [smoothMinMaxGradient, minMaxRowGradient_single]

omit [Nonempty ι] [Nonempty κ] in
theorem minMaxRowHessian_single_of_row_ne [DecidableEq ι] [DecidableEq κ]
    (x : (ι × κ) → ℝ) (i j l : ι) (k m : κ) (hjl : j ≠ l) :
    minMaxRowHessian x i (Pi.single (j, k) 1) (Pi.single (l, m) 1) = 0 := by
  by_cases hij : i = j
  · subst i
    simp [minMaxRowHessian, minMaxRow_single, hjl]
  · simp [minMaxRowHessian, minMaxRow_single, hij]

omit [Nonempty ι] [Nonempty κ] in
theorem smoothMinMaxHessian_single_of_row_ne [DecidableEq ι] [DecidableEq κ]
    (x : (ι × κ) → ℝ) (j l : ι) (k m : κ) (hjl : j ≠ l) :
    smoothMinMaxHessian x (Pi.single (j, k) 1) (Pi.single (l, m) 1) =
      minMaxRowWeight x l * (minMaxRowWeight x j * softmaxWeight (minMaxRow j x) k) *
        softmaxWeight (minMaxRow l x) m := by
  simp [smoothMinMaxHessian, minMaxRowWeightDerivative,
    minMaxRowHessian_single_of_row_ne, minMaxRowGradient_single,
    smoothMinMaxGradient_single, hjl, Ne.symm hjl]

omit [Nonempty κ] in
theorem minMaxRowWeight_pos (x : (ι × κ) → ℝ) (i : ι) : 0 < minMaxRowWeight x i :=
  softmaxWeight_pos _ i

omit [Nonempty κ] in
theorem sum_minMaxRowWeight (x : (ι × κ) → ℝ) : ∑ i, minMaxRowWeight x i = 1 :=
  sum_softmaxWeight _

theorem smoothMinMaxHessian_single_pos_of_row_ne [DecidableEq ι] [DecidableEq κ]
    (x : (ι × κ) → ℝ) (j l : ι) (k m : κ) (hjl : j ≠ l) :
    0 < smoothMinMaxHessian x (Pi.single (j, k) 1) (Pi.single (l, m) 1) := by
  rw [smoothMinMaxHessian_single_of_row_ne x j l k m hjl]
  exact mul_pos (mul_pos (minMaxRowWeight_pos x l)
    (mul_pos (minMaxRowWeight_pos x j) (softmaxWeight_pos _ k))) (softmaxWeight_pos _ m)

end ConvexBodyChasing

end
end BundledModule085

/- Component source: ConvexBodyChasing.SmoothMinMaxBounds -/
section BundledModule086
/-! # Global bounds for smooth finite min–max

The gradient has norm at most one and the Hessian has norm at most four.
These bounds justify Gaussian integration and differentiation.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators
namespace ConvexBodyChasing

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty ι] [Nonempty κ]

omit [Nonempty ι] [Nonempty κ] in
theorem norm_minMaxRow_le (i : ι) : ‖(minMaxRow (κ := κ) i)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  exact (pi_norm_le_iff_of_nonneg (by positivity)).mpr (fun j => by
    simpa only [minMaxRow, ContinuousLinearMap.pi_apply, ContinuousLinearMap.proj_apply,
      one_mul] using! norm_le_pi_norm v (i, j))

omit [Nonempty ι] [Nonempty κ] in
theorem norm_minMaxRow_apply_le (i : ι) (v : (ι × κ) → ℝ) : ‖minMaxRow i v‖ ≤ ‖v‖ := by
  exact ((minMaxRow i).le_opNorm v).trans (by
    simpa only [one_mul] using! mul_le_mul_of_nonneg_right (norm_minMaxRow_le i) (norm_nonneg v))

omit [Nonempty ι] in
theorem norm_minMaxRowGradient_le (x : (ι × κ) → ℝ) (i : ι) :
    ‖minMaxRowGradient x i‖ ≤ 1 := by
  calc
    ‖minMaxRowGradient x i‖ ≤ ‖logSumExpGradient (minMaxRow i x)‖ * ‖minMaxRow i‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * 1 := mul_le_mul (norm_logSumExpGradient_le _) (norm_minMaxRow_le i)
      (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

omit [Nonempty ι] in
theorem norm_minMaxRowHessian_le (x : (ι × κ) → ℝ) (i : ι) :
    ‖minMaxRowHessian x i‖ ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound₂ _ (by norm_num)
  intro v w
  change ‖logSumExpHessian (minMaxRow i x) (minMaxRow i v) (minMaxRow i w)‖ ≤ _
  calc
    _ ≤ ‖logSumExpHessian (minMaxRow i x)‖ * ‖minMaxRow i v‖ * ‖minMaxRow i w‖ :=
      ContinuousLinearMap.le_opNorm₂ _ _ _
    _ ≤ 2 * ‖v‖ * ‖w‖ := by
      gcongr
      · exact norm_logSumExpHessian_le _
      · exact norm_minMaxRow_apply_le _ _
      · exact norm_minMaxRow_apply_le _ _

theorem norm_smoothMinMaxGradient_le (x : (ι × κ) → ℝ) : ‖smoothMinMaxGradient x‖ ≤ 1 := by
  calc
    ‖smoothMinMaxGradient x‖ ≤ ∑ i, ‖minMaxRowWeight x i • minMaxRowGradient x i‖ :=
      norm_sum_le Finset.univ (fun i => minMaxRowWeight x i • minMaxRowGradient x i)
    _ ≤ ∑ i, minMaxRowWeight x i := Finset.sum_le_sum (fun i _ => by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (minMaxRowWeight_pos x i)]
      exact mul_le_of_le_one_right (minMaxRowWeight_pos x i).le (norm_minMaxRowGradient_le x i))
    _ = 1 := sum_minMaxRowWeight x

theorem norm_minMaxRowWeightDerivative_le (x : (ι × κ) → ℝ) (i : ι) :
    ‖minMaxRowWeightDerivative x i‖ ≤ minMaxRowWeight x i * 2 := by
  rw [minMaxRowWeightDerivative, norm_smul, Real.norm_eq_abs,
    abs_of_pos (minMaxRowWeight_pos x i)]
  apply mul_le_mul_of_nonneg_left _ (minMaxRowWeight_pos x i).le
  exact (norm_sub_le _ _).trans (by
    linarith [norm_smoothMinMaxGradient_le x, norm_minMaxRowGradient_le x i])

theorem norm_smoothMinMaxHessian_le (x : (ι × κ) → ℝ) : ‖smoothMinMaxHessian x‖ ≤ 4 := by
  letI : NormSMulClass ℝ (((ι × κ) → ℝ) →L[ℝ] ((ι × κ) → ℝ) →L[ℝ] ℝ) :=
    NormedSpace.toNormSMulClass (𝕜 := ℝ)
      (E := ((ι × κ) → ℝ) →L[ℝ] ((ι × κ) → ℝ) →L[ℝ] ℝ)
  calc
    ‖smoothMinMaxHessian x‖ ≤ ∑ i, ‖(minMaxRowWeightDerivative x i).smulRight
        (minMaxRowGradient x i) + minMaxRowWeight x i • minMaxRowHessian x i‖ :=
      norm_sum_le Finset.univ (fun i => (minMaxRowWeightDerivative x i).smulRight
        (minMaxRowGradient x i) + minMaxRowWeight x i • minMaxRowHessian x i)
    _ ≤ ∑ i, minMaxRowWeight x i * 4 := Finset.sum_le_sum (fun i _ => by
      refine (norm_add_le ((minMaxRowWeightDerivative x i).smulRight (minMaxRowGradient x i))
        (minMaxRowWeight x i • minMaxRowHessian x i)).trans ?_
      rw [ContinuousLinearMap.norm_smulRight_apply, norm_smul, Real.norm_eq_abs,
        abs_of_pos (minMaxRowWeight_pos x i)]
      calc
        _ ≤ minMaxRowWeight x i * 2 + minMaxRowWeight x i * 2 := add_le_add
          ((mul_le_of_le_one_right (norm_nonneg _) (norm_minMaxRowGradient_le x i)).trans
            (norm_minMaxRowWeightDerivative_le x i))
          (mul_le_mul_of_nonneg_left (norm_minMaxRowHessian_le x i) (minMaxRowWeight_pos x i).le)
        _ = _ := by ring)
    _ = 4 := by rw [← Finset.sum_mul, sum_minMaxRowWeight, one_mul]

omit [Nonempty ι] in
theorem continuous_minMaxRowHessian (i : ι) :
    Continuous (fun x : (ι × κ) → ℝ => minMaxRowHessian x i) := by
  exact continuous_const.clm_comp
    (((continuous_logSumExpHessian (ι := κ)).comp (minMaxRow (κ := κ) i).continuous).clm_comp_const
      (minMaxRow (κ := κ) i))

omit [Nonempty ι] in
theorem continuous_minMaxRowGradient (i : ι) :
    Continuous (fun x : (ι × κ) → ℝ => minMaxRowGradient x i) :=
  continuous_iff_continuousAt.mpr (fun x => (hasFDerivAt_minMaxRowGradient x i).continuousAt)

theorem continuous_smoothMinMaxGradient : Continuous (smoothMinMaxGradient (ι := ι) (κ := κ)) :=
  continuous_iff_continuousAt.mpr (fun x => (hasFDerivAt_smoothMinMaxGradient x).continuousAt)

theorem continuous_minMaxRowWeight (i : ι) :
    Continuous (fun x : (ι × κ) → ℝ => minMaxRowWeight x i) :=
  continuous_iff_continuousAt.mpr (fun x => (hasFDerivAt_minMaxRowWeight x i).continuousAt)

theorem continuous_minMaxRowWeightDerivative (i : ι) :
    Continuous (fun x : (ι × κ) → ℝ => minMaxRowWeightDerivative x i) := by
  exact (continuous_minMaxRowWeight i).smul
    (continuous_smoothMinMaxGradient.sub (continuous_minMaxRowGradient i))

theorem continuous_smoothMinMaxHessian : Continuous (smoothMinMaxHessian (ι := ι) (κ := κ)) := by
  letI : ContinuousAdd (((ι × κ) → ℝ) →L[ℝ] ((ι × κ) → ℝ) →L[ℝ] ℝ) :=
    (inferInstance : IsTopologicalAddGroup
      (((ι × κ) → ℝ) →L[ℝ] ((ι × κ) → ℝ) →L[ℝ] ℝ)).toContinuousAdd
  exact continuous_finset_sum _ (fun i _ =>
    (((ContinuousLinearMap.smulRightL ℝ ((ι × κ) → ℝ)
      (((ι × κ) → ℝ) →L[ℝ] ℝ)).continuous.comp
        (continuous_minMaxRowWeightDerivative i)).clm_apply (continuous_minMaxRowGradient i)).add
      ((continuous_minMaxRowWeight i).smul (continuous_minMaxRowHessian i)))

end ConvexBodyChasing

end
end BundledModule086

/- Component source: ConvexBodyChasing.FiniteMinMax -/
section BundledModule087
/-! # Finite min–max and uniform smooth approximation -/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators
namespace ConvexBodyChasing

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty ι] [Nonempty κ]

def finiteRowMax (x : (ι × κ) → ℝ) (i : ι) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun j => x (i, j))

def finiteMinMax (x : (ι × κ) → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (finiteRowMax x)

omit [Fintype ι] [Nonempty ι] in
theorem coordinate_le_finiteRowMax (x : (ι × κ) → ℝ) (i : ι) (j : κ) :
    x (i, j) ≤ finiteRowMax x i :=
  Finset.le_sup' (fun j => x (i, j)) (Finset.mem_univ j)

theorem finiteMinMax_le_finiteRowMax (x : (ι × κ) → ℝ) (i : ι) :
    finiteMinMax x ≤ finiteRowMax x i :=
  Finset.inf'_le _ (Finset.mem_univ i)

omit [Fintype ι] [Nonempty ι] in
theorem finiteRowMax_le_minMaxRowValues (x : (ι × κ) → ℝ) (i : ι) :
    finiteRowMax x i ≤ minMaxRowValues x i := by
  exact Finset.sup'_le _ _ (fun j _ => coordinate_le_logSumExp (minMaxRow i x) j)

omit [Fintype ι] [Nonempty ι] in
theorem minMaxRowValues_le_finiteRowMax (x : (ι × κ) → ℝ) (i : ι) :
    minMaxRowValues x i ≤ finiteRowMax x i + Real.log (Fintype.card κ) := by
  exact logSumExp_le_of_coordinate_le (minMaxRow i x) (finiteRowMax x i)
    (coordinate_le_finiteRowMax x i)

theorem finiteMinMax_sub_log_le_smoothMinMax (x : (ι × κ) → ℝ) :
    finiteMinMax x - Real.log (Fintype.card ι) ≤ smoothMinMax x := by
  have h := logSumExp_le_of_coordinate_le (-minMaxRowValues x) (-finiteMinMax x)
    (fun i => neg_le_neg ((finiteMinMax_le_finiteRowMax x i).trans
      (finiteRowMax_le_minMaxRowValues x i)))
  change _ ≤ -logSumExp (-minMaxRowValues x)
  linarith

theorem smoothMinMax_le_finiteMinMax_add_log (x : (ι × κ) → ℝ) :
    smoothMinMax x ≤ finiteMinMax x + Real.log (Fintype.card κ) := by
  have h : smoothMinMax x - Real.log (Fintype.card κ) ≤ finiteMinMax x := by
    apply Finset.le_inf' _ _
    intro i _
    have h₁ := coordinate_le_logSumExp (-minMaxRowValues x) i
    have h₂ := minMaxRowValues_le_finiteRowMax x i
    change -minMaxRowValues x i ≤ logSumExp (-minMaxRowValues x) at h₁
    change -logSumExp (-minMaxRowValues x) - _ ≤ _
    linarith
  linarith

theorem continuous_finiteMinMax : Continuous (finiteMinMax (ι := ι) (κ := κ)) := by
  exact Continuous.finset_inf'_apply Finset.univ_nonempty (fun i _ =>
    Continuous.finset_sup'_apply Finset.univ_nonempty (fun j _ => continuous_apply (i, j)))

theorem norm_finiteMinMax_le (x : (ι × κ) → ℝ) : ‖finiteMinMax x‖ ≤ ‖x‖ := by
  have hc : ∀ a, |x a| ≤ ‖x‖ := fun a => norm_le_pi_norm x a
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · apply Finset.le_inf' _ _
    intro i _
    let j : κ := Classical.choice inferInstance
    exact (abs_le.mp (hc (i, j))).1.trans (coordinate_le_finiteRowMax x i j)
  · let i : ι := Classical.choice inferInstance
    refine (finiteMinMax_le_finiteRowMax x i).trans ?_
    exact Finset.sup'_le _ _ (fun j _ => (abs_le.mp (hc (i, j))).2)

omit [Fintype ι] [Nonempty ι] in
theorem finiteRowMax_smul (x : (ι × κ) → ℝ) (i : ι) {c : ℝ} (hc : 0 < c) :
    finiteRowMax (c • x) i = c * finiteRowMax x i := by
  exact (map_finset_sup' (OrderIso.mulLeft₀ c hc) Finset.univ_nonempty
    (fun j => x (i, j))).symm

theorem finiteMinMax_smul (x : (ι × κ) → ℝ) {c : ℝ} (hc : 0 < c) :
    finiteMinMax (c • x) = c * finiteMinMax x := by
  simp only [finiteMinMax, finiteRowMax_smul _ _ hc]
  exact (map_finset_inf' (OrderIso.mulLeft₀ c hc) Finset.univ_nonempty (finiteRowMax x)).symm

end ConvexBodyChasing

end
end BundledModule087

/- Component source: ConvexBodyChasing.GaussianIntegrationByParts -/
section BundledModule088
/-! # Gaussian integration by parts

The standard Gaussian density satisfies its differential equation. Integration
by parts then gives Stein's identity with all integrability conditions explicit.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open MeasureTheory ProbabilityTheory
namespace ConvexBodyChasing

theorem hasDerivAt_standardGaussianDensity (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1)
      (-x * gaussianPDFReal 0 1 x) x := by
  unfold gaussianPDFReal
  simp only [NNReal.coe_one, mul_one, sub_zero]
  convert! (((hasDerivAt_id x).pow 2).neg.div_const 2).exp.const_mul
    (Real.sqrt (2 * Real.pi))⁻¹ using 1
  simp only [Pi.neg_apply, Pi.pow_apply, id_eq]
  ring

theorem integrable_standardGaussian_iff {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : ℝ → E) :
    Integrable f (gaussianReal 0 1) ↔
      Integrable (fun x => gaussianPDFReal 0 1 x • f x) := by
  rw [gaussianReal_of_var_ne_zero 0 one_ne_zero]
  simpa only [toReal_gaussianPDF] using!
    (integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 1)
      (Filter.Eventually.of_forall (fun _ => gaussianPDF_lt_top)) (g := f))

/-- Stein's identity for the standard real Gaussian, with integrability proved by
the caller for the function, its derivative, and the coordinate product. -/
theorem integral_standardGaussian_mul_eq_deriv {f f' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x)
    (hi : Integrable f (gaussianReal 0 1))
    (hi' : Integrable f' (gaussianReal 0 1))
    (hxi : Integrable (fun x => x * f x) (gaussianReal 0 1)) :
    ∫ x, x * f x ∂gaussianReal 0 1 = ∫ x, f' x ∂gaussianReal 0 1 := by
  have hfg : Integrable (fun x => (-x * gaussianPDFReal 0 1 x) * f x) := by
    simpa only [smul_eq_mul, neg_mul, mul_assoc, mul_left_comm] using!
      ((integrable_standardGaussian_iff _).mp hxi).neg
  have h := integral_mul_deriv_eq_deriv_mul_of_integrable
    (fun x _ => hasDerivAt_standardGaussianDensity x) (fun x _ => hf x)
    ((integrable_standardGaussian_iff _).mp hi') hfg
    ((integrable_standardGaussian_iff _).mp hi)
  simpa only [integral_gaussianReal_eq_integral_smul (v := 1) one_ne_zero,
    smul_eq_mul, neg_mul, mul_assoc, mul_left_comm, integral_neg, neg_neg] using! h.symm

/-- The bounded version discharges all Gaussian integrability hypotheses. -/
theorem integral_standardGaussian_mul_eq_deriv_of_bounded {f f' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (C C' : ℝ)
    (hC : ∀ x, ‖f x‖ ≤ C) (hC' : ∀ x, ‖f' x‖ ≤ C') :
    ∫ x, x * f x ∂gaussianReal 0 1 = ∫ x, f' x ∂gaussianReal 0 1 := by
  have hfm : AEStronglyMeasurable f (gaussianReal 0 1) :=
    (continuous_iff_continuousAt.mpr (fun x => (hf x).continuousAt)).aestronglyMeasurable
  have hf'm : AEStronglyMeasurable f' (gaussianReal 0 1) :=
    (aestronglyMeasurable_deriv f _).congr (Filter.Eventually.of_forall (fun x => (hf x).deriv))
  exact integral_standardGaussian_mul_eq_deriv hf
    (memLp_one_iff_integrable.mp (MemLp.of_bound hfm C (Filter.Eventually.of_forall hC)))
    (memLp_one_iff_integrable.mp (MemLp.of_bound hf'm C' (Filter.Eventually.of_forall hC')))
    ((memLp_one_iff_integrable.mp (memLp_id_gaussianReal' 1 (by simp))).mul_bdd hfm
      (Filter.Eventually.of_forall hC))

/-- Fubini's theorem with one Gaussian coordinate singled out. -/
theorem integral_coordinateGaussian_succAbove {n : ℕ} (i : Fin (n + 1))
    {f : (Fin (n + 1) → ℝ) → ℝ} (hf : Integrable f (coordinateGaussian (Fin (n + 1)))) :
    ∫ x, f x ∂coordinateGaussian (Fin (n + 1)) =
      ∫ z, ∫ t, f (i.insertNth t z) ∂gaussianReal 0 1 ∂coordinateGaussian (Fin n) := by
  have he := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => gaussianReal 0 1) i).symm
  rw [show coordinateGaussian (Fin (n + 1)) = Measure.pi (fun _ => gaussianReal 0 1) from rfl,
    ← he.integral_comp' f]
  exact integral_prod_symm _ (he.integrable_comp_of_integrable hf)

/-- Coordinate Stein identity for a bounded function with bounded coordinate derivative. -/
theorem integral_coordinateGaussian_mul_eq_partial {n : ℕ} (i : Fin (n + 1))
    {f f' : (Fin (n + 1) → ℝ) → ℝ} (hfm : Continuous f) (hf'm : Continuous f')
    (hf : ∀ z t, HasDerivAt (fun s => f (i.insertNth s z)) (f' (i.insertNth t z)) t)
    (C C' : ℝ) (hC : ∀ x, ‖f x‖ ≤ C) (hC' : ∀ x, ‖f' x‖ ≤ C') :
    ∫ x, x i * f x ∂coordinateGaussian (Fin (n + 1)) =
      ∫ x, f' x ∂coordinateGaussian (Fin (n + 1)) := by
  have hi : Integrable (fun x : Fin (n + 1) → ℝ => x i * f x)
      (coordinateGaussian (Fin (n + 1))) :=
    ((coordinateGaussian_eval (Fin (n + 1)) i).integrable_comp_of_integrable
      (memLp_one_iff_integrable.mp (memLp_id_gaussianReal' 1 (by simp)))).mul_bdd hfm.aestronglyMeasurable
        (Filter.Eventually.of_forall hC)
  have hi' : Integrable f' (coordinateGaussian (Fin (n + 1))) :=
    memLp_one_iff_integrable.mp (MemLp.of_bound hf'm.aestronglyMeasurable C'
      (Filter.Eventually.of_forall hC'))
  rw [integral_coordinateGaussian_succAbove i hi, integral_coordinateGaussian_succAbove i hi']
  exact integral_congr_ae (Filter.Eventually.of_forall (fun z => by
    simpa only [Fin.insertNth_apply_same] using!
      integral_standardGaussian_mul_eq_deriv_of_bounded (hf z) C C'
        (fun t => hC (i.insertNth t z)) (fun t => hC' (i.insertNth t z))))

/-- The derivative along a coordinate insertion is its coordinate unit vector. -/
theorem hasDerivAt_insertNth {n : ℕ} (i : Fin (n + 1)) (z : Fin n → ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => i.insertNth (α := fun _ => ℝ) s z)
      (Pi.single i (1 : ℝ)) t := by
  convert! hasDerivAt_update (i.insertNth 0 z) i t using 1
  exact funext (fun s => (Fin.update_insertNth (α := fun _ => ℝ) i 0 s z).symm)



end ConvexBodyChasing

end
end BundledModule088

/- Component source: ConvexBodyChasing.GaussianInterpolation -/
section BundledModule089
/-! # Differentiation of Gaussian expectations along linear images

Bounded first derivatives give integrable domination. The coordinate Stein
identity then expresses the variation using second derivatives.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open MeasureTheory
open scoped BigOperators NNReal
namespace ConvexBodyChasing

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A globally bounded derivative gives a global Lipschitz bound. -/
theorem lipschitzWith_of_hasFDerivAt_bound {f : E → ℝ} {df : E → E →L[ℝ] ℝ}
    (hf : ∀ x, HasFDerivAt f (df x) x) (C : ℝ≥0) (hC : ∀ x, ‖df x‖ ≤ C) :
    LipschitzWith C f := by
  apply lipschitzWith_of_nnnorm_fderiv_le (fun x => (hf x).differentiableAt)
  exact fun x => (NNReal.coe_le_coe).mp (by simpa only [(hf x).fderiv] using! hC x)

/-- Lipschitz functions of finite Gaussian linear images have finite second moment. -/
theorem memLp_gaussian_lipschitz_linear {ι : Type*} [Fintype ι]
    {f : E → ℝ} {C : ℝ≥0} (hf : LipschitzWith C f) (L : (ι → ℝ) →L[ℝ] E) :
    MemLp (fun x => f (L x)) 2 (coordinateGaussian ι) := by
  have hs : LipschitzWith C (fun x => f x - f 0) :=
    fun x y => by simpa only [edist_sub_right] using! hf x y
  have h := (hs.comp_memLp (by simp)
    (L.comp_memLp' (coordinateGaussian_memLp_id ι))).add (memLp_const (f 0))
  change MemLp (fun x => f (L x) - f 0 + f 0) 2 (coordinateGaussian ι) at h
  simpa only [sub_add_cancel] using! h

/-- Differentiation under the Gaussian integral along a linear-operator path.
The dominating function is a constant times the Gaussian coordinate norm. -/
theorem hasDerivAt_gaussian_integral_linear_path {ι : Type*} [Fintype ι]
    {f : E → ℝ} {df : E → E →L[ℝ] ℝ}
    (hf : ∀ x, HasFDerivAt f (df x) x) (hdf : Continuous df)
    {T T' : ℝ → (ι → ℝ) →L[ℝ] E} (hT : ∀ t, HasDerivAt T (T' t) t)
    (C K : ℝ≥0) (hC : ∀ x, ‖df x‖ ≤ C) (hK : ∀ t, ‖T' t‖ ≤ K) (t : ℝ) :
    HasDerivAt (fun s => ∫ x, f (T s x) ∂coordinateGaussian ι)
      (∫ x, df (T t x) (T' t x) ∂coordinateGaussian ι) t := by
  have hfc : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hf x).continuousAt)
  have hb (s : ℝ) (x : ι → ℝ) : ‖df (T s x) (T' s x)‖ ≤ (C : ℝ) * K * ‖x‖ := by
    simpa only [mul_assoc] using!
      (df (T s x)).le_of_opNorm_le_of_le (hC (T s x)) ((T' s).le_of_opNorm_le (hK s) x)
  have hdT (s : ℝ) (x : ι → ℝ) : HasDerivAt (fun r => T r x) (T' s x) s := by
    simpa only [map_zero, add_zero] using! (hT s).clm_apply (hasDerivAt_const s x)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Set.univ) (bound := fun x : ι → ℝ => (C : ℝ) * K * ‖x‖) Filter.univ_mem
    (Filter.Eventually.of_forall (fun s => (hfc.comp (T s).continuous).aestronglyMeasurable))
    ((memLp_gaussian_lipschitz_linear (lipschitzWith_of_hasFDerivAt_bound hf C hC)
      (T t)).integrable (by norm_num))
    (((hdf.comp (T t).continuous).clm_apply (T' t).continuous).aestronglyMeasurable)
    (Filter.Eventually.of_forall (fun x s _ => hb s x))
    (((coordinateGaussian_memLp_id ι).integrable (by norm_num)).norm.const_mul ((C : ℝ) * K))
    (Filter.Eventually.of_forall (fun x s _ => (hf (T s x)).comp_hasDerivAt s (hdT s x)))).2

/-- Stein's identity for a bounded gradient composed with a Gaussian linear image. -/
theorem integral_gaussian_gradient_coordinate {n : ℕ} (i : Fin (n + 1))
    {df : E → E →L[ℝ] ℝ} {ddf : E → E →L[ℝ] E →L[ℝ] ℝ}
    (hd : ∀ u, HasFDerivAt df (ddf u) u) (hdd : Continuous ddf)
    (C₁ C₂ : ℝ≥0) (hC₁ : ∀ u, ‖df u‖ ≤ C₁) (hC₂ : ∀ u, ‖ddf u‖ ≤ C₂)
    (L : (Fin (n + 1) → ℝ) →L[ℝ] E) (v : E) :
    ∫ x, x i * df (L x) v ∂coordinateGaussian (Fin (n + 1)) =
      ∫ x, ddf (L x) (L (Pi.single i 1)) v ∂coordinateGaussian (Fin (n + 1)) := by
  have hdc : Continuous df := continuous_iff_continuousAt.mpr (fun u => (hd u).continuousAt)
  have hpart (z : Fin n → ℝ) (t : ℝ) :
      HasDerivAt (fun s => df (L (i.insertNth s z)) v)
        (ddf (L (i.insertNth t z)) (L (Pi.single i 1)) v) t := by
    simpa only [map_zero, add_zero] using!
      ((hd _).comp_hasDerivAt t
        (L.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_insertNth i z t))).clm_apply
          (hasDerivAt_const t v)
  exact integral_coordinateGaussian_mul_eq_partial i
    ((hdc.comp L.continuous).clm_apply continuous_const)
    (((hdd.comp L.continuous).clm_apply continuous_const).clm_apply continuous_const)
    hpart ((C₁ : ℝ) * ‖v‖) ((C₂ : ℝ) * ‖L (Pi.single i 1)‖ * ‖v‖)
    (fun x => (df (L x)).le_of_opNorm_le (hC₁ (L x)) v)
    (fun x => (ddf (L x) (L (Pi.single i 1))).le_of_opNorm_le
      ((ddf (L x)).le_of_opNorm_le (hC₂ (L x)) (L (Pi.single i 1))) v)

/-- The Gaussian gradient pairing equals its integrated Hessian trace. -/
theorem integral_gaussian_gradient_linear {n : ℕ}
    {df : E → E →L[ℝ] ℝ} {ddf : E → E →L[ℝ] E →L[ℝ] ℝ}
    (hd : ∀ u, HasFDerivAt df (ddf u) u) (hdd : Continuous ddf)
    (C₁ C₂ : ℝ≥0) (hC₁ : ∀ u, ‖df u‖ ≤ C₁) (hC₂ : ∀ u, ‖ddf u‖ ≤ C₂)
    (L M : (Fin (n + 1) → ℝ) →L[ℝ] E) :
    ∫ x, df (L x) (M x) ∂coordinateGaussian (Fin (n + 1)) =
      ∑ i : Fin (n + 1), ∫ x, ddf (L x) (L (Pi.single i 1)) (M (Pi.single i 1))
        ∂coordinateGaussian (Fin (n + 1)) := by
  have hdc : Continuous df := continuous_iff_continuousAt.mpr (fun u => (hd u).continuousAt)
  have hpoint (x : Fin (n + 1) → ℝ) :
      df (L x) (M x) = ∑ i, x i * df (L x) (M (Pi.single i 1)) := by
    simpa only [map_sum, map_smul, smul_eq_mul, Pi.basisFun_apply, Pi.basisFun_repr] using!
      congrArg (fun y => df (L x) (M y)) ((Pi.basisFun ℝ (Fin (n + 1))).sum_repr x).symm
  have hi (i : Fin (n + 1)) : Integrable
      (fun x => x i * df (L x) (M (Pi.single i 1))) (coordinateGaussian (Fin (n + 1))) :=
    ((coordinateGaussian_eval (Fin (n + 1)) i).integrable_comp_of_integrable
      (memLp_one_iff_integrable.mp (ProbabilityTheory.memLp_id_gaussianReal' 1 (by simp)))).mul_bdd
        ((hdc.comp L.continuous).clm_apply continuous_const).aestronglyMeasurable
        (Filter.Eventually.of_forall (fun x =>
          (df (L x)).le_of_opNorm_le (hC₁ (L x)) (M (Pi.single i 1))))
  rw [integral_congr_ae (Filter.Eventually.of_forall hpoint),
    integral_finset_sum Finset.univ (fun i _ => hi i)]
  exact Finset.sum_congr rfl (fun i _ =>
    integral_gaussian_gradient_coordinate i hd hdd C₁ C₂ hC₁ hC₂ L (M (Pi.single i 1)))

/-- Gaussian interpolation formula in terms of the actual Hessian. -/
theorem hasDerivAt_gaussian_integral_hessian {n : ℕ}
    {f : E → ℝ} {df : E → E →L[ℝ] ℝ} {ddf : E → E →L[ℝ] E →L[ℝ] ℝ}
    (hf : ∀ u, HasFDerivAt f (df u) u) (hd : ∀ u, HasFDerivAt df (ddf u) u)
    (hdd : Continuous ddf) {T T' : ℝ → (Fin (n + 1) → ℝ) →L[ℝ] E}
    (hT : ∀ t, HasDerivAt T (T' t) t) (C₁ C₂ K : ℝ≥0)
    (hC₁ : ∀ u, ‖df u‖ ≤ C₁) (hC₂ : ∀ u, ‖ddf u‖ ≤ C₂) (hK : ∀ t, ‖T' t‖ ≤ K)
    (t : ℝ) :
    HasDerivAt (fun s => ∫ x, f (T s x) ∂coordinateGaussian (Fin (n + 1)))
      (∑ i : Fin (n + 1), ∫ x,
        ddf (T t x) (T t (Pi.single i 1)) (T' t (Pi.single i 1))
          ∂coordinateGaussian (Fin (n + 1))) t := by
  have h := hasDerivAt_gaussian_integral_linear_path hf
    (continuous_iff_continuousAt.mpr (fun u => (hd u).continuousAt)) hT C₁ K hC₁ hK t
  simpa only [integral_gaussian_gradient_linear hd hdd C₁ C₂ hC₁ hC₂] using! h

end ConvexBodyChasing

end
end BundledModule089

/- Component source: ConvexBodyChasing.GaussianRotation -/
section BundledModule090
/-! # Gaussian comparison by rotation

Independent linear images can be placed on disjoint Gaussian coordinates.
Rotation interpolates between their expectations without singular endpoints.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open MeasureTheory
open scoped BigOperators NNReal
namespace ConvexBodyChasing

variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

def gaussianRotationPath (A B : V →L[ℝ] E) (t : ℝ) : V →L[ℝ] E :=
  Real.cos t • A + Real.sin t • B

def gaussianRotationDerivative (A B : V →L[ℝ] E) (t : ℝ) : V →L[ℝ] E :=
  -Real.sin t • A + Real.cos t • B

theorem hasDerivAt_gaussianRotationPath (A B : V →L[ℝ] E) (t : ℝ) :
    HasDerivAt (gaussianRotationPath A B) (gaussianRotationDerivative A B t) t := by
  exact ((Real.hasDerivAt_cos t).smul_const A).add ((Real.hasDerivAt_sin t).smul_const B)

theorem norm_gaussianRotationDerivative_le (A B : V →L[ℝ] E) (t : ℝ) :
    ‖gaussianRotationDerivative A B t‖ ≤ ‖A‖ + ‖B‖ := by
  refine (norm_add_le _ _).trans ?_
  simpa only [norm_smul, norm_neg, Real.norm_eq_abs, one_mul] using!
    add_le_add (mul_le_mul_of_nonneg_right (Real.abs_sin_le_one t) (norm_nonneg A))
      (mul_le_mul_of_nonneg_right (Real.abs_cos_le_one t) (norm_nonneg B))

/-- The mixed bilinear terms vanish when one of the two vectors is zero. -/
theorem bilinear_rotation_of_disjoint (H : E →L[ℝ] E →L[ℝ] ℝ) (a b : E)
    (hab : a = 0 ∨ b = 0) (s c : ℝ) :
    H (c • a + s • b) (-s • a + c • b) = s * c * (H b b - H a a) := by
  rcases hab with rfl | rfl <;>
    simp only [smul_zero, zero_add, add_zero, map_smul, map_zero,
      ContinuousLinearMap.smul_apply, smul_eq_mul] <;> ring

/-- Integrability of a bounded bilinear field evaluated on two fixed vectors. -/
theorem integrable_gaussian_bilinear_apply {ι : Type*} [Fintype ι]
    {H : E → E →L[ℝ] E →L[ℝ] ℝ} (hH : Continuous H) (C : ℝ≥0)
    (hC : ∀ u, ‖H u‖ ≤ C) (L : (ι → ℝ) →L[ℝ] E) (a b : E) :
    Integrable (fun x => H (L x) a b) (coordinateGaussian ι) := by
  exact memLp_one_iff_integrable.mp (MemLp.of_bound
    (((hH.comp L.continuous).clm_apply continuous_const).clm_apply continuous_const).aestronglyMeasurable
    ((C : ℝ) * ‖a‖ * ‖b‖) (Filter.Eventually.of_forall (fun x =>
      (H (L x) a).le_of_opNorm_le ((H (L x)).le_of_opNorm_le (hC (L x)) a) b)))

/-- Gaussian expectation comparison from the signed Hessian trace.
Disjoint source coordinates realize independent linear images. -/
theorem gaussian_rotation_comparison {n : ℕ}
    {f : E → ℝ} {df : E → E →L[ℝ] ℝ} {ddf : E → E →L[ℝ] E →L[ℝ] ℝ}
    (hf : ∀ u, HasFDerivAt f (df u) u) (hd : ∀ u, HasFDerivAt df (ddf u) u)
    (hdd : Continuous ddf) (C₁ C₂ : ℝ≥0)
    (hC₁ : ∀ u, ‖df u‖ ≤ C₁) (hC₂ : ∀ u, ‖ddf u‖ ≤ C₂)
    (A B : (Fin (n + 1) → ℝ) →L[ℝ] E)
    (hdisjoint : ∀ i, A (Pi.single i 1) = 0 ∨ B (Pi.single i 1) = 0)
    (htrace : ∀ u, 0 ≤ ∑ i : Fin (n + 1),
      (ddf u (B (Pi.single i 1)) (B (Pi.single i 1)) -
        ddf u (A (Pi.single i 1)) (A (Pi.single i 1)))) :
    ∫ x, f (A x) ∂coordinateGaussian (Fin (n + 1)) ≤
      ∫ x, f (B x) ∂coordinateGaussian (Fin (n + 1)) := by
  have hderiv (t : ℝ) := hasDerivAt_gaussian_integral_hessian hf hd hdd
    (hasDerivAt_gaussianRotationPath A B) C₁ C₂ (‖A‖₊ + ‖B‖₊) hC₁ hC₂
    (norm_gaussianRotationDerivative_le A B) t
  have heq (t : ℝ) (u : E) :
      (∑ i : Fin (n + 1), ddf u
        (gaussianRotationPath A B t (Pi.single i 1))
        (gaussianRotationDerivative A B t (Pi.single i 1))) =
      Real.sin t * Real.cos t * ∑ i : Fin (n + 1),
        (ddf u (B (Pi.single i 1)) (B (Pi.single i 1)) -
          ddf u (A (Pi.single i 1)) (A (Pi.single i 1))) := by
    simp only [gaussianRotationPath, gaussianRotationDerivative,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => bilinear_rotation_of_disjoint (ddf u)
      (A (Pi.single i 1)) (B (Pi.single i 1)) (hdisjoint i) (Real.sin t) (Real.cos t))
  have hn (t : ℝ) (ht : t ∈ Set.Icc 0 (Real.pi / 2)) :
      0 ≤ ∑ i : Fin (n + 1), ∫ x,
        ddf (gaussianRotationPath A B t x)
          (gaussianRotationPath A B t (Pi.single i 1))
          (gaussianRotationDerivative A B t (Pi.single i 1))
            ∂coordinateGaussian (Fin (n + 1)) := by
    rw [← integral_finset_sum Finset.univ (fun i _ =>
      integrable_gaussian_bilinear_apply hdd C₂ hC₂ (gaussianRotationPath A B t)
        (gaussianRotationPath A B t (Pi.single i 1))
        (gaussianRotationDerivative A B t (Pi.single i 1)))]
    refine integral_nonneg (fun x => ?_)
    rw [heq]
    exact mul_nonneg (mul_nonneg
      (Real.sin_nonneg_of_nonneg_of_le_pi ht.1 (by linarith [ht.2, Real.pi_pos]))
      (Real.cos_nonneg_of_mem_Icc ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩)) (htrace _)
  have hm := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (0 : ℝ) (Real.pi / 2))
    (continuous_iff_continuousAt.mpr (fun t => (hderiv t).continuousAt)).continuousOn
    (fun t _ => (hderiv t).hasDerivWithinAt) (fun t ht => hn t (interior_subset ht))
  simpa only [gaussianRotationPath, Real.cos_zero, Real.sin_zero, Real.cos_pi_div_two,
    Real.sin_pi_div_two, one_smul, zero_smul, add_zero, zero_add] using!
    hm (show (0 : ℝ) ∈ Set.Icc 0 (Real.pi / 2) from ⟨le_rfl, by positivity⟩)
      (show Real.pi / 2 ∈ Set.Icc 0 (Real.pi / 2) from ⟨by positivity, le_rfl⟩) (by positivity)

end ConvexBodyChasing

end
end BundledModule090

/- Component source: ConvexBodyChasing.GaussianCovarianceComparison -/
section BundledModule091
/-! # Covariance coordinates for Gaussian comparison

The coefficients in the comparison are the actual covariances of the linear
Gaussian images. Expanding the Hessian gives their signed trace pairing.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace ConvexBodyChasing

variable {ι κ E : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem continuousLinearMap_apply_eq_sum_single (L : (ι → ℝ) →L[ℝ] E) (x : ι → ℝ) :
    L x = ∑ i, x i • L (Pi.single i 1) := by
  simpa only [map_sum, map_smul, Pi.basisFun_apply, Pi.basisFun_repr] using!
    congrArg L ((Pi.basisFun ℝ ι).sum_repr x).symm

omit [DecidableEq κ] in
theorem continuousLinearMap_coordinate_apply (A : (ι → ℝ) →L[ℝ] (κ → ℝ))
    (x : ι → ℝ) (j : κ) : A x j = ∑ i, A (Pi.single i 1) j * x i := by
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm] using!
    congrFun (continuousLinearMap_apply_eq_sum_single A x) j

omit [DecidableEq κ] in
/-- The row Gram matrix is the covariance of the actual Gaussian image. -/
theorem covariance_gaussian_linear_image (A : (ι → ℝ) →L[ℝ] (κ → ℝ)) (j k : κ) :
    covariance (fun x => A x j) (fun x => A x k) (coordinateGaussian ι) =
      ∑ i, A (Pi.single i 1) j * A (Pi.single i 1) k := by
  rw [funext (fun x => continuousLinearMap_coordinate_apply A x j),
    funext (fun x => continuousLinearMap_coordinate_apply A x k)]
  exact coordinateGaussian_covariance_linear ι (fun i => A (Pi.single i 1) j)
    (fun i => A (Pi.single i 1) k)

/-- Coordinate expansion of a real bilinear form. -/
theorem bilinear_apply_eq_sum_single (H : (κ → ℝ) →L[ℝ] (κ → ℝ) →L[ℝ] ℝ)
    (x y : κ → ℝ) :
    H x y = ∑ j, ∑ k, H (Pi.single j 1) (Pi.single k 1) * (x j * y k) := by
  rw [continuousLinearMap_apply_eq_sum_single H x]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simpa only [smul_eq_mul, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] using!
    congrArg (fun z : ℝ => x j * z)
      (continuousLinearMap_apply_eq_sum_single (H (Pi.single j 1)) y)

/-- Contracting a bilinear form with Gaussian columns is its covariance pairing. -/
theorem sum_bilinear_gaussian_covariance
    (H : (κ → ℝ) →L[ℝ] (κ → ℝ) →L[ℝ] ℝ) (A : (ι → ℝ) →L[ℝ] (κ → ℝ)) :
    (∑ i, H (A (Pi.single i 1)) (A (Pi.single i 1))) =
      ∑ j, ∑ k, H (Pi.single j 1) (Pi.single k 1) *
        covariance (fun x => A x j) (fun x => A x k) (coordinateGaussian ι) := by
  have he : (∑ i, H (A (Pi.single i 1)) (A (Pi.single i 1))) =
      ∑ i, ∑ j, ∑ k, H (Pi.single j 1) (Pi.single k 1) *
        (A (Pi.single i 1) j * A (Pi.single i 1) k) :=
    Finset.sum_congr rfl (fun i _ => bilinear_apply_eq_sum_single H _ _)
  rw [he, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, covariance_gaussian_linear_image]

/-- Smooth Gaussian comparison from coordinate covariance and Hessian signs. -/
theorem gaussian_covariance_comparison {n : ℕ}
    {f : (κ → ℝ) → ℝ} {df : (κ → ℝ) → (κ → ℝ) →L[ℝ] ℝ}
    {ddf : (κ → ℝ) → (κ → ℝ) →L[ℝ] (κ → ℝ) →L[ℝ] ℝ}
    (hf : ∀ u, HasFDerivAt f (df u) u) (hd : ∀ u, HasFDerivAt df (ddf u) u)
    (hdd : Continuous ddf) (C₁ C₂ : ℝ≥0)
    (hC₁ : ∀ u, ‖df u‖ ≤ C₁) (hC₂ : ∀ u, ‖ddf u‖ ≤ C₂)
    (A B : (Fin (n + 1) → ℝ) →L[ℝ] (κ → ℝ))
    (hdisjoint : ∀ i, A (Pi.single i 1) = 0 ∨ B (Pi.single i 1) = 0)
    (hcov : ∀ u j k, 0 ≤ ddf u (Pi.single j 1) (Pi.single k 1) *
      (covariance (fun x => B x j) (fun x => B x k) (coordinateGaussian (Fin (n + 1))) -
        covariance (fun x => A x j) (fun x => A x k) (coordinateGaussian (Fin (n + 1))))) :
    ∫ x, f (A x) ∂coordinateGaussian (Fin (n + 1)) ≤
      ∫ x, f (B x) ∂coordinateGaussian (Fin (n + 1)) := by
  apply gaussian_rotation_comparison hf hd hdd C₁ C₂ hC₁ hC₂ A B hdisjoint
  intro u
  rw [Finset.sum_sub_distrib, sum_bilinear_gaussian_covariance, sum_bilinear_gaussian_covariance]
  simpa only [mul_sub, Finset.sum_sub_distrib] using!
    Finset.sum_nonneg (s := Finset.univ) (fun j _ =>
      Finset.sum_nonneg (s := Finset.univ) (fun k _ => hcov u j k))

end ConvexBodyChasing

end
end BundledModule091

/- Component source: ConvexBodyChasing.GaussianFiniteMinMax -/
section BundledModule092
/-! # Finite Gaussian min–max comparison

Within each row the covariances agree; between distinct rows, increasing the
covariance increases the expected minimum of the row maxima.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace ConvexBodyChasing

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty ι] [Nonempty κ]
  [DecidableEq ι] [DecidableEq κ] {n : ℕ}

omit [DecidableEq ι] [DecidableEq κ] in
theorem integrable_gaussian_finiteMinMax
    (A : (Fin (n + 1) → ℝ) →L[ℝ] ((ι × κ) → ℝ)) :
    Integrable (fun x => finiteMinMax (A x)) (coordinateGaussian (Fin (n + 1))) := by
  exact ((A.comp_memLp' (coordinateGaussian_memLp_id (Fin (n + 1)))).integrable (by norm_num)).norm.mono'
    (continuous_finiteMinMax.comp A.continuous).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => norm_finiteMinMax_le (A x)))

omit [DecidableEq ι] [DecidableEq κ] in
theorem integrable_gaussian_smoothMinMax
    (A : (Fin (n + 1) → ℝ) →L[ℝ] ((ι × κ) → ℝ)) :
    Integrable (fun x => smoothMinMax (A x)) (coordinateGaussian (Fin (n + 1))) := by
  have h : LipschitzWith 1 (smoothMinMax (ι := ι) (κ := κ)) :=
    lipschitzWith_of_hasFDerivAt_bound hasFDerivAt_smoothMinMax 1 norm_smoothMinMaxGradient_le
  exact (memLp_gaussian_lipschitz_linear h A).integrable (by norm_num)

omit [Nonempty ι] [Nonempty κ] [DecidableEq ι] [DecidableEq κ] in
theorem covariance_gaussian_smul_image
    (A : (Fin (n + 1) → ℝ) →L[ℝ] ((ι × κ) → ℝ)) (c : ℝ) (a b : ι × κ) :
    covariance (fun x => (c • A) x a) (fun x => (c • A) x b)
      (coordinateGaussian (Fin (n + 1))) =
        c ^ 2 * covariance (fun x => A x a) (fun x => A x b)
          (coordinateGaussian (Fin (n + 1))) := by
  rw [covariance_gaussian_linear_image (c • A) a b, covariance_gaussian_linear_image A a b]
  simp only [ContinuousLinearMap.smul_apply,
    Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

omit [DecidableEq ι] [DecidableEq κ] in
theorem gaussian_finiteMinMax_sub_log_le_smooth
    (A : (Fin (n + 1) → ℝ) →L[ℝ] ((ι × κ) → ℝ)) :
    (∫ x, finiteMinMax (A x) ∂coordinateGaussian (Fin (n + 1))) - Real.log (Fintype.card ι) ≤
      ∫ x, smoothMinMax (A x) ∂coordinateGaussian (Fin (n + 1)) := by
  have h := integral_mono ((integrable_gaussian_finiteMinMax A).sub
    (integrable_const (Real.log (Fintype.card ι)))) (integrable_gaussian_smoothMinMax A)
    (fun x => finiteMinMax_sub_log_le_smoothMinMax (A x))
  simpa [integral_sub (integrable_gaussian_finiteMinMax A)
    (integrable_const (Real.log (Fintype.card ι)))] using! h

omit [DecidableEq ι] [DecidableEq κ] in
theorem gaussian_smooth_le_finiteMinMax_add_log
    (A : (Fin (n + 1) → ℝ) →L[ℝ] ((ι × κ) → ℝ)) :
    (∫ x, smoothMinMax (A x) ∂coordinateGaussian (Fin (n + 1))) ≤
      (∫ x, finiteMinMax (A x) ∂coordinateGaussian (Fin (n + 1))) + Real.log (Fintype.card κ) := by
  have h := integral_mono (integrable_gaussian_smoothMinMax A)
    ((integrable_gaussian_finiteMinMax A).add (integrable_const (Real.log (Fintype.card κ))))
    (fun x => smoothMinMax_le_finiteMinMax_add_log (A x))
  simpa [integral_add (integrable_gaussian_finiteMinMax A)
    (integrable_const (Real.log (Fintype.card κ)))] using! h

omit [DecidableEq ι] [DecidableEq κ] in
theorem integral_gaussian_finiteMinMax_smul
    (A : (Fin (n + 1) → ℝ) →L[ℝ] ((ι × κ) → ℝ)) {c : ℝ} (hc : 0 < c) :
    (∫ x, finiteMinMax ((c • A) x) ∂coordinateGaussian (Fin (n + 1))) =
      c * ∫ x, finiteMinMax (A x) ∂coordinateGaussian (Fin (n + 1)) := by
  simp only [ContinuousLinearMap.smul_apply, finiteMinMax_smul _ hc, integral_const_mul]

theorem gaussian_smoothMinMax_comparison
    (A B : (Fin (n + 1) → ℝ) →L[ℝ] ((ι × κ) → ℝ))
    (hdisjoint : ∀ i, A (Pi.single i 1) = 0 ∨ B (Pi.single i 1) = 0)
    (hrow : ∀ a b : ι × κ, a.1 = b.1 →
      covariance (fun x => A x a) (fun x => A x b) (coordinateGaussian (Fin (n + 1))) =
        covariance (fun x => B x a) (fun x => B x b) (coordinateGaussian (Fin (n + 1))))
    (hcov : ∀ a b : ι × κ, a.1 ≠ b.1 →
      covariance (fun x => A x a) (fun x => A x b) (coordinateGaussian (Fin (n + 1))) ≤
        covariance (fun x => B x a) (fun x => B x b) (coordinateGaussian (Fin (n + 1)))) :
    ∫ x, smoothMinMax (A x) ∂coordinateGaussian (Fin (n + 1)) ≤
      ∫ x, smoothMinMax (B x) ∂coordinateGaussian (Fin (n + 1)) := by
  apply gaussian_covariance_comparison hasFDerivAt_smoothMinMax
    hasFDerivAt_smoothMinMaxGradient continuous_smoothMinMaxHessian 1 4
    norm_smoothMinMaxGradient_le norm_smoothMinMaxHessian_le A B hdisjoint
  rintro u ⟨i, j⟩ ⟨k, l⟩
  by_cases hik : i = k
  · rw [hrow (i, j) (k, l) hik, sub_self, mul_zero]
  · exact mul_nonneg (smoothMinMaxHessian_single_pos_of_row_ne u i k j l hik).le
      (sub_nonneg.mpr (hcov (i, j) (k, l) hik))

/-- Gaussian comparison for the actual finite minimum of row maxima. -/
theorem gaussian_finiteMinMax_comparison
    (A B : (Fin (n + 1) → ℝ) →L[ℝ] ((ι × κ) → ℝ))
    (hdisjoint : ∀ i, A (Pi.single i 1) = 0 ∨ B (Pi.single i 1) = 0)
    (hrow : ∀ a b : ι × κ, a.1 = b.1 →
      covariance (fun x => A x a) (fun x => A x b) (coordinateGaussian (Fin (n + 1))) =
        covariance (fun x => B x a) (fun x => B x b) (coordinateGaussian (Fin (n + 1))))
    (hcov : ∀ a b : ι × κ, a.1 ≠ b.1 →
      covariance (fun x => A x a) (fun x => A x b) (coordinateGaussian (Fin (n + 1))) ≤
        covariance (fun x => B x a) (fun x => B x b) (coordinateGaussian (Fin (n + 1)))) :
    ∫ x, finiteMinMax (A x) ∂coordinateGaussian (Fin (n + 1)) ≤
      ∫ x, finiteMinMax (B x) ∂coordinateGaussian (Fin (n + 1)) := by
  have hs (c : ℝ) (hc : 0 < c) :
      c * (∫ x, finiteMinMax (A x) ∂coordinateGaussian (Fin (n + 1))) -
        Real.log (Fintype.card ι) ≤
      c * (∫ x, finiteMinMax (B x) ∂coordinateGaussian (Fin (n + 1))) +
        Real.log (Fintype.card κ) := by
    have hcomp : (∫ x, smoothMinMax ((c • A) x) ∂coordinateGaussian (Fin (n + 1))) ≤
        ∫ x, smoothMinMax ((c • B) x) ∂coordinateGaussian (Fin (n + 1)) := by
      apply gaussian_smoothMinMax_comparison
      · intro i
        rcases hdisjoint i with h | h <;> simp [ContinuousLinearMap.smul_apply, h]
      · intro a b hab
        rw [covariance_gaussian_smul_image, covariance_gaussian_smul_image, hrow a b hab]
      · intro a b hab
        rw [covariance_gaussian_smul_image, covariance_gaussian_smul_image]
        exact mul_le_mul_of_nonneg_left (hcov a b hab) (sq_nonneg c)
    simpa only [integral_gaussian_finiteMinMax_smul _ hc] using!
      (gaussian_finiteMinMax_sub_log_le_smooth (c • A)).trans
        (hcomp.trans (gaussian_smooth_le_finiteMinMax_add_log (c • B)))
  by_contra h
  let D := (∫ x, finiteMinMax (A x) ∂coordinateGaussian (Fin (n + 1))) -
    ∫ x, finiteMinMax (B x) ∂coordinateGaussian (Fin (n + 1))
  have hD : 0 < D := sub_pos.mpr (lt_of_not_ge h)
  let C : ℝ := Real.log (Fintype.card ι) + Real.log (Fintype.card κ)
  have hscale := hs ((|C| + 1) / D) (div_pos (by positivity) hD)
  have hm : ((|C| + 1) / D) * D = |C| + 1 := div_mul_cancel₀ _ hD.ne'
  have hb : ((|C| + 1) / D) * D ≤ C := by
    dsimp [D, C]
    nlinarith [hscale]
  linarith [le_abs_self C]

end ConvexBodyChasing

end
end BundledModule092

/- Component source: ConvexBodyChasing.GaussianReindex -/
section BundledModule093
/-! # Reindexing finite standard Gaussian coordinates

Coordinate equivalences preserve the actual product Gaussian measure. This
extends the finite min–max comparison to arbitrary finite source index types.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open MeasureTheory ProbabilityTheory
namespace ConvexBodyChasing

variable {η ζ : Type*} [Fintype η] [Fintype ζ]

def gaussianReindex (e : η ≃ ζ) : (η → ℝ) →L[ℝ] (ζ → ℝ) :=
  ContinuousLinearMap.pi (fun j => ContinuousLinearMap.proj (e.symm j))

omit [Fintype η] [Fintype ζ] in
theorem gaussianReindex_apply (e : η ≃ ζ) (x : η → ℝ) (j : ζ) :
    gaussianReindex e x j = x (e.symm j) := rfl

omit [Fintype η] [Fintype ζ] in
theorem gaussianReindex_eq_measurableEquiv (e : η ≃ ζ) :
    (gaussianReindex e : (η → ℝ) → (ζ → ℝ)) = MeasurableEquiv.piCongrLeft (fun _ : ζ => ℝ) e := by
  ext x j
  simp [gaussianReindex_apply, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]

theorem gaussianReindex_preserving (e : η ≃ ζ) :
    MeasurePreserving (gaussianReindex e) (coordinateGaussian η) (coordinateGaussian ζ) := by
  rw [gaussianReindex_eq_measurableEquiv]
  exact measurePreserving_piCongrLeft (fun _ : ζ => gaussianReal 0 1) e

theorem integral_gaussianReindex (e : η ≃ ζ) (f : (ζ → ℝ) → ℝ) :
    ∫ x, f (gaussianReindex e x) ∂coordinateGaussian η = ∫ y, f y ∂coordinateGaussian ζ := by
  rw [gaussianReindex_eq_measurableEquiv]
  exact (measurePreserving_piCongrLeft (fun _ : ζ => gaussianReal 0 1) e).integral_comp' f

theorem covariance_gaussianReindex (e : η ≃ ζ) (f g : (ζ → ℝ) → ℝ) :
    covariance (fun x => f (gaussianReindex e x)) (fun x => g (gaussianReindex e x))
      (coordinateGaussian η) = covariance f g (coordinateGaussian ζ) := by
  have hp := gaussianReindex_preserving e
  rw [gaussianReindex_eq_measurableEquiv] at hp ⊢
  simpa only [hp.map_eq, Function.comp_apply] using!
    (covariance_map_equiv (μ := coordinateGaussian η) f g
      (MeasurableEquiv.piCongrLeft (fun _ : ζ => ℝ) e)).symm

omit [Fintype η] [Fintype ζ] in
theorem gaussianReindex_single [DecidableEq η] [DecidableEq ζ] (e : η ≃ ζ) (i : η) :
    gaussianReindex e (Pi.single i 1) = Pi.single (e i) 1 := by
  ext j
  simp [gaussianReindex_apply, Pi.single_apply, Equiv.eq_symm_apply, eq_comm]

theorem gaussian_finiteMinMax_comparison_of_fintype
    {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty ι] [Nonempty κ]
    [DecidableEq ι] [DecidableEq κ] [DecidableEq η] [Nonempty η]
    (A B : (η → ℝ) →L[ℝ] ((ι × κ) → ℝ))
    (hdisjoint : ∀ i, A (Pi.single i 1) = 0 ∨ B (Pi.single i 1) = 0)
    (hrow : ∀ a b : ι × κ, a.1 = b.1 →
      covariance (fun x => A x a) (fun x => A x b) (coordinateGaussian η) =
        covariance (fun x => B x a) (fun x => B x b) (coordinateGaussian η))
    (hcov : ∀ a b : ι × κ, a.1 ≠ b.1 →
      covariance (fun x => A x a) (fun x => A x b) (coordinateGaussian η) ≤
        covariance (fun x => B x a) (fun x => B x b) (coordinateGaussian η)) :
    ∫ x, finiteMinMax (A x) ∂coordinateGaussian η ≤
      ∫ x, finiteMinMax (B x) ∂coordinateGaussian η := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Fintype.card_ne_zero (α := η))
  let e : Fin (n + 1) ≃ η := (Fintype.equivFinOfCardEq hn).symm
  have h := gaussian_finiteMinMax_comparison (A.comp (gaussianReindex e)) (B.comp (gaussianReindex e))
    (fun i => by simpa only [ContinuousLinearMap.comp_apply, gaussianReindex_single] using! hdisjoint (e i))
    (fun a b hab => by
      simp only [ContinuousLinearMap.comp_apply]
      rw [covariance_gaussianReindex e (fun x => A x a) (fun x => A x b),
        covariance_gaussianReindex e (fun x => B x a) (fun x => B x b)]
      exact hrow a b hab)
    (fun a b hab => by
      simp only [ContinuousLinearMap.comp_apply]
      rw [covariance_gaussianReindex e (fun x => A x a) (fun x => A x b),
        covariance_gaussianReindex e (fun x => B x a) (fun x => B x b)]
      exact hcov a b hab)
  simp only [ContinuousLinearMap.comp_apply] at h
  rwa [integral_gaussianReindex e (fun x => finiteMinMax (A x)),
    integral_gaussianReindex e (fun x => finiteMinMax (B x))] at h

end ConvexBodyChasing

end
end BundledModule093

/- Component source: ConvexBodyChasing.GordonProcesses -/
section BundledModule094
/-! # The Gaussian processes in Gordon's comparison

Separate source coordinates carry a matrix and scalar, and two vectors. Their
covariances are computed from the actual product standard Gaussian measure.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators InnerProductSpace
namespace ConvexBodyChasing
namespace Gordon

abbrev Source (α β : Type*) := ((α × β) ⊕ Unit) ⊕ (β ⊕ α)

variable {α β ι κ : Type*} [Fintype α] [Fintype β] [Fintype ι] [Fintype κ]

def matrixCoefficient (x : EuclideanSpace ℝ α) (y : EuclideanSpace ℝ β) : Source α β → ℝ
  | .inl (.inl (a, b)) => x a * y b
  | .inl (.inr ()) => 1
  | .inr _ => 0

def vectorCoefficient (x : EuclideanSpace ℝ α) (y : EuclideanSpace ℝ β) : Source α β → ℝ
  | .inl _ => 0
  | .inr (.inl b) => y b
  | .inr (.inr a) => x a

def matrixProcess (x : ι → EuclideanSpace ℝ α) (y : κ → EuclideanSpace ℝ β) :
    (Source α β → ℝ) →L[ℝ] ((ι × κ) → ℝ) :=
  ContinuousLinearMap.pi (fun ij => gaussianLinearFunctional (Source α β)
    (matrixCoefficient (x ij.1) (y ij.2)))

def vectorProcess (x : ι → EuclideanSpace ℝ α) (y : κ → EuclideanSpace ℝ β) :
    (Source α β → ℝ) →L[ℝ] ((ι × κ) → ℝ) :=
  ContinuousLinearMap.pi (fun ij => gaussianLinearFunctional (Source α β)
    (vectorCoefficient (x ij.1) (y ij.2)))

theorem sum_mul_coordinates (x x' : EuclideanSpace ℝ α) :
    (∑ a, x a * x' a) = ⟪x, x'⟫_ℝ := by
  simp [PiLp.inner_apply, mul_comm]

theorem sum_vectorCoefficient_mul (x x' : EuclideanSpace ℝ α) (y y' : EuclideanSpace ℝ β) :
    (∑ s, vectorCoefficient x y s * vectorCoefficient x' y' s) = ⟪y, y'⟫_ℝ + ⟪x, x'⟫_ℝ := by
  simp [vectorCoefficient, Fintype.sum_sum_type, sum_mul_coordinates]

theorem sum_matrixCoefficient_mul (x x' : EuclideanSpace ℝ α) (y y' : EuclideanSpace ℝ β) :
    (∑ s, matrixCoefficient x y s * matrixCoefficient x' y' s) =
      ⟪x, x'⟫_ℝ * ⟪y, y'⟫_ℝ + 1 := by
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, matrixCoefficient,
    Fintype.sum_unique, mul_one, zero_mul, Finset.sum_const_zero, add_zero]
  rw [← sum_mul_coordinates x x', ← sum_mul_coordinates y y']
  rw [Finset.sum_mul]
  simp only [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

omit [Fintype ι] [Fintype κ] in
theorem covariance_vectorProcess (x : ι → EuclideanSpace ℝ α) (y : κ → EuclideanSpace ℝ β)
    (a b : ι × κ) :
    covariance (fun g => vectorProcess x y g a) (fun g => vectorProcess x y g b)
      (coordinateGaussian (Source α β)) = ⟪y a.2, y b.2⟫_ℝ + ⟪x a.1, x b.1⟫_ℝ := by
  simp only [vectorProcess, ContinuousLinearMap.pi_apply, gaussianLinearFunctional_apply,
    coordinateGaussian_covariance_linear, sum_vectorCoefficient_mul]

omit [Fintype ι] [Fintype κ] in
theorem covariance_matrixProcess (x : ι → EuclideanSpace ℝ α) (y : κ → EuclideanSpace ℝ β)
    (a b : ι × κ) :
    covariance (fun g => matrixProcess x y g a) (fun g => matrixProcess x y g b)
      (coordinateGaussian (Source α β)) = ⟪x a.1, x b.1⟫_ℝ * ⟪y a.2, y b.2⟫_ℝ + 1 := by
  simp only [matrixProcess, ContinuousLinearMap.pi_apply, gaussianLinearFunctional_apply,
    coordinateGaussian_covariance_linear, sum_matrixCoefficient_mul]

omit [Fintype ι] [Fintype κ] in
theorem matrixProcess_single [DecidableEq α] [DecidableEq β]
    (x : ι → EuclideanSpace ℝ α) (y : κ → EuclideanSpace ℝ β) (s : Source α β) (a : ι × κ) :
    matrixProcess x y (Pi.single s 1) a = matrixCoefficient (x a.1) (y a.2) s := by
  simp [matrixProcess, gaussianLinearFunctional_apply, Pi.single_apply]

omit [Fintype ι] [Fintype κ] in
theorem vectorProcess_single [DecidableEq α] [DecidableEq β]
    (x : ι → EuclideanSpace ℝ α) (y : κ → EuclideanSpace ℝ β) (s : Source α β) (a : ι × κ) :
    vectorProcess x y (Pi.single s 1) a = vectorCoefficient (x a.1) (y a.2) s := by
  simp [vectorProcess, gaussianLinearFunctional_apply, Pi.single_apply]

omit [Fintype ι] [Fintype κ] in
theorem processes_disjoint [DecidableEq α] [DecidableEq β]
    (x : ι → EuclideanSpace ℝ α) (y : κ → EuclideanSpace ℝ β) (s : Source α β) :
    vectorProcess x y (Pi.single s 1) = 0 ∨ matrixProcess x y (Pi.single s 1) = 0 := by
  cases s with
  | inl s =>
    left
    ext a
    simp [vectorProcess_single, vectorCoefficient]
  | inr s =>
    right
    ext a
    simp [matrixProcess_single, matrixCoefficient]

omit [Fintype ι] [Fintype κ] in
theorem covariance_difference (x : ι → EuclideanSpace ℝ α) (y : κ → EuclideanSpace ℝ β)
    (a b : ι × κ) :
    covariance (fun g => matrixProcess x y g a) (fun g => matrixProcess x y g b)
        (coordinateGaussian (Source α β)) -
      covariance (fun g => vectorProcess x y g a) (fun g => vectorProcess x y g b)
        (coordinateGaussian (Source α β)) =
      (1 - ⟪x a.1, x b.1⟫_ℝ) * (1 - ⟪y a.2, y b.2⟫_ℝ) := by
  rw [covariance_matrixProcess, covariance_vectorProcess]
  ring

/-- Gordon's process comparison for finite collections of Euclidean unit vectors. -/
theorem finite_process_comparison [Nonempty ι] [Nonempty κ]
    (x : ι → EuclideanSpace ℝ α) (y : κ → EuclideanSpace ℝ β)
    (hx : ∀ i, ‖x i‖ = 1) (hy : ∀ j, ‖y j‖ = 1) :
    ∫ g, finiteMinMax (vectorProcess x y g) ∂coordinateGaussian (Source α β) ≤
      ∫ g, finiteMinMax (matrixProcess x y g) ∂coordinateGaussian (Source α β) := by
  classical
  apply gaussian_finiteMinMax_comparison_of_fintype _ _ (processes_disjoint x y)
  · intro a b hab
    rw [covariance_vectorProcess, covariance_matrixProcess, hab, real_inner_self_eq_norm_sq,
      hx, one_pow, one_mul]
  · intro a b _
    apply sub_nonneg.mp
    rw [covariance_difference]
    apply mul_nonneg
    · exact sub_nonneg.mpr (by simpa [hx] using! real_inner_le_norm (x a.1) (x b.1))
    · exact sub_nonneg.mpr (by simpa [hy] using! real_inner_le_norm (y a.2) (y b.2))

end Gordon
end ConvexBodyChasing

end
end BundledModule094

/- Component source: ConvexBodyChasing.FiniteExtrema -/
section BundledModule095
/-! # Finite extrema used in Gaussian comparison

Translations separate row and column terms in finite min–max. Negation
interchanges the finite minimum and maximum.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace ConvexBodyChasing

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty ι] [Nonempty κ]

def finiteMaximum (x : ι → ℝ) : ℝ := Finset.univ.sup' Finset.univ_nonempty x

def finiteMinimum (x : ι → ℝ) : ℝ := Finset.univ.inf' Finset.univ_nonempty x

theorem finiteMinMax_eq_min_max (x : (ι × κ) → ℝ) :
    finiteMinMax x = finiteMinimum (fun i => finiteMaximum (fun j => x (i, j))) := rfl

theorem finiteMaximum_add_const (x : ι → ℝ) (c : ℝ) :
    finiteMaximum (fun i => x i + c) = finiteMaximum x + c := by
  exact (map_finset_sup' (OrderIso.addRight c) Finset.univ_nonempty x).symm

theorem finiteMinimum_add_const (x : ι → ℝ) (c : ℝ) :
    finiteMinimum (fun i => x i + c) = finiteMinimum x + c := by
  exact (map_finset_inf' (OrderIso.addRight c) Finset.univ_nonempty x).symm

theorem finiteMinimum_neg (x : ι → ℝ) : finiteMinimum (-x) = -finiteMaximum x := by
  exact (map_finset_sup' (OrderIso.neg ℝ) Finset.univ_nonempty x).symm

theorem finiteMinMax_add_const (x : (ι × κ) → ℝ) (c : ℝ) :
    finiteMinMax (fun a => x a + c) = finiteMinMax x + c := by
  simp only [finiteMinMax_eq_min_max, finiteMaximum_add_const, finiteMinimum_add_const]

theorem finiteMinMax_separable (f : ι → ℝ) (g : κ → ℝ) :
    finiteMinMax (fun a => f a.1 + g a.2) = finiteMinimum f + finiteMaximum g := by
  simp only [finiteMinMax_eq_min_max, add_comm (f _) (g _), finiteMaximum_add_const]
  simp only [add_comm (finiteMaximum g) (f _), finiteMinimum_add_const]

theorem continuous_finiteMaximum : Continuous (finiteMaximum (ι := ι)) :=
  Continuous.finset_sup'_apply Finset.univ_nonempty (fun i _ => continuous_apply i)

theorem continuous_finiteMinimum : Continuous (finiteMinimum (ι := ι)) :=
  Continuous.finset_inf'_apply Finset.univ_nonempty (fun i _ => continuous_apply i)

theorem norm_finiteMaximum_le (x : ι → ℝ) : ‖finiteMaximum x‖ ≤ ‖x‖ := by
  have hc : ∀ i, |x i| ≤ ‖x‖ := fun i => norm_le_pi_norm x i
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · let i : ι := Classical.choice inferInstance
    exact (abs_le.mp (hc i)).1.trans (Finset.le_sup' x (Finset.mem_univ i))
  · exact Finset.sup'_le _ _ (fun i _ => (abs_le.mp (hc i)).2)

theorem norm_finiteMinimum_le (x : ι → ℝ) : ‖finiteMinimum x‖ ≤ ‖x‖ := by
  have hc : ∀ i, |x i| ≤ ‖x‖ := fun i => norm_le_pi_norm x i
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · exact Finset.le_inf' _ _ (fun i _ => (abs_le.mp (hc i)).1)
  · let i : ι := Classical.choice inferInstance
    exact (Finset.inf'_le x (Finset.mem_univ i)).trans (abs_le.mp (hc i)).2

end ConvexBodyChasing

end
end BundledModule095

/- Component source: ConvexBodyChasing.GaussianExtrema -/
section BundledModule096
/-! # Integrability and symmetry of finite Gaussian extrema -/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open MeasureTheory
namespace ConvexBodyChasing

variable {η ι κ : Type*} [Fintype η] [Fintype ι] [Fintype κ] [Nonempty ι] [Nonempty κ]

theorem integrable_gaussian_finiteMaximum (A : (η → ℝ) →L[ℝ] (ι → ℝ)) :
    Integrable (fun x => finiteMaximum (A x)) (coordinateGaussian η) := by
  exact ((A.comp_memLp' (coordinateGaussian_memLp_id η)).integrable (by norm_num)).norm.mono'
    (continuous_finiteMaximum.comp A.continuous).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => norm_finiteMaximum_le (A x)))

theorem integrable_gaussian_finiteMinimum (A : (η → ℝ) →L[ℝ] (ι → ℝ)) :
    Integrable (fun x => finiteMinimum (A x)) (coordinateGaussian η) := by
  exact ((A.comp_memLp' (coordinateGaussian_memLp_id η)).integrable (by norm_num)).norm.mono'
    (continuous_finiteMinimum.comp A.continuous).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => norm_finiteMinimum_le (A x)))

theorem integrable_gaussian_finiteMinMax_of_fintype (A : (η → ℝ) →L[ℝ] ((ι × κ) → ℝ)) :
    Integrable (fun x => finiteMinMax (A x)) (coordinateGaussian η) := by
  exact ((A.comp_memLp' (coordinateGaussian_memLp_id η)).integrable (by norm_num)).norm.mono'
    (continuous_finiteMinMax.comp A.continuous).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => norm_finiteMinMax_le (A x)))

theorem integral_gaussian_finiteMinimum_eq_neg_maximum (A : (η → ℝ) →L[ℝ] (ι → ℝ)) :
    (∫ x, finiteMinimum (A x) ∂coordinateGaussian η) =
      -(∫ x, finiteMaximum (A x) ∂coordinateGaussian η) := by
  have hp : MeasurePreserving (MeasurableEquiv.neg (η → ℝ))
      (coordinateGaussian η) (coordinateGaussian η) := coordinateGaussian_neg_preserving η
  have h := hp.integral_comp' (fun x => finiteMinimum (A x))
  simpa only [MeasurableEquiv.neg_apply, map_neg, finiteMinimum_neg, integral_neg] using! h.symm

end ConvexBodyChasing

end
end BundledModule096

/- Component source: ConvexBodyChasing.GordonFinite -/
section BundledModule097
/-! # Finite Gordon expectation inequality

The scalar in the matrix process has mean zero. Separating the two vector
terms and using Gaussian symmetry gives the expected-maximum difference.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ConvexBodyChasing.Gordon

variable {α β ι κ : Type*} [Fintype α] [Fintype β] [Fintype ι] [Fintype κ]

def rowVectorValues (x : ι → EuclideanSpace ℝ α) : (Source α β → ℝ) →L[ℝ] (ι → ℝ) :=
  ContinuousLinearMap.pi (fun i => ∑ a, x i a • ContinuousLinearMap.proj (.inr (.inr a)))

def columnVectorValues (y : κ → EuclideanSpace ℝ β) : (Source α β → ℝ) →L[ℝ] (κ → ℝ) :=
  ContinuousLinearMap.pi (fun j => ∑ b, y j b • ContinuousLinearMap.proj (.inr (.inl b)))

def matrixValues (x : ι → EuclideanSpace ℝ α) (y : κ → EuclideanSpace ℝ β) :
    (Source α β → ℝ) →L[ℝ] ((ι × κ) → ℝ) :=
  ContinuousLinearMap.pi (fun ij => ∑ a, ∑ b,
    (x ij.1 a * y ij.2 b) • ContinuousLinearMap.proj (.inl (.inl (a, b))))

omit [Fintype ι] [Fintype κ] in
theorem vectorProcess_apply (x : ι → EuclideanSpace ℝ α) (y : κ → EuclideanSpace ℝ β)
    (g : Source α β → ℝ) (a : ι × κ) :
    vectorProcess x y g a = rowVectorValues x g a.1 + columnVectorValues y g a.2 := by
  simp [vectorProcess, gaussianLinearFunctional_apply, Fintype.sum_sum_type,
    vectorCoefficient, rowVectorValues, columnVectorValues, add_comm]

omit [Fintype ι] [Fintype κ] in
theorem matrixProcess_apply (x : ι → EuclideanSpace ℝ α) (y : κ → EuclideanSpace ℝ β)
    (g : Source α β → ℝ) (a : ι × κ) :
    matrixProcess x y g a = matrixValues x y g a + g (.inl (.inr ())) := by
  simp [matrixProcess, gaussianLinearFunctional_apply, Fintype.sum_sum_type,
    Fintype.sum_prod_type, matrixCoefficient, matrixValues]

theorem finiteMinMax_vectorProcess [Nonempty ι] [Nonempty κ]
    (x : ι → EuclideanSpace ℝ α) (y : κ → EuclideanSpace ℝ β) (g : Source α β → ℝ) :
    finiteMinMax (vectorProcess x y g) =
      finiteMinimum (rowVectorValues x g) + finiteMaximum (columnVectorValues y g) := by
  rw [show vectorProcess x y g = (fun a => rowVectorValues x g a.1 + columnVectorValues y g a.2)
    from funext (vectorProcess_apply x y g)]
  exact finiteMinMax_separable _ _

theorem finiteMinMax_matrixProcess [Nonempty ι] [Nonempty κ]
    (x : ι → EuclideanSpace ℝ α) (y : κ → EuclideanSpace ℝ β) (g : Source α β → ℝ) :
    finiteMinMax (matrixProcess x y g) = finiteMinMax (matrixValues x y g) + g (.inl (.inr ())) := by
  rw [show matrixProcess x y g = (fun a => matrixValues x y g a + g (.inl (.inr ())))
    from funext (matrixProcess_apply x y g)]
  exact finiteMinMax_add_const _ _

theorem integral_vectorProcess [Nonempty ι] [Nonempty κ]
    (x : ι → EuclideanSpace ℝ α) (y : κ → EuclideanSpace ℝ β) :
    (∫ g, finiteMinMax (vectorProcess x y g) ∂coordinateGaussian (Source α β)) =
      (∫ g, finiteMaximum (columnVectorValues y g) ∂coordinateGaussian (Source α β)) -
        ∫ g, finiteMaximum (rowVectorValues x g) ∂coordinateGaussian (Source α β) := by
  simp only [finiteMinMax_vectorProcess]
  rw [integral_add (integrable_gaussian_finiteMinimum (rowVectorValues (β := β) x))
    (integrable_gaussian_finiteMaximum (columnVectorValues (α := α) y)),
    integral_gaussian_finiteMinimum_eq_neg_maximum]
  ring

theorem integral_matrixProcess [Nonempty ι] [Nonempty κ]
    (x : ι → EuclideanSpace ℝ α) (y : κ → EuclideanSpace ℝ β) :
    (∫ g, finiteMinMax (matrixProcess x y g) ∂coordinateGaussian (Source α β)) =
      ∫ g, finiteMinMax (matrixValues x y g) ∂coordinateGaussian (Source α β) := by
  have hi : Integrable (fun g : Source α β → ℝ => g (.inl (.inr ())))
      (coordinateGaussian (Source α β)) := by
    simpa only [id_eq] using!
      (((coordinateGaussian_memLp_id (Source α β)).eval (.inl (.inr ()))).integrable (by norm_num))
  simp only [finiteMinMax_matrixProcess]
  rw [integral_add (integrable_gaussian_finiteMinMax_of_fintype (matrixValues x y)) hi,
    coordinateGaussian_mean, add_zero]

/-- The finite Gordon expectation bound for unit vectors in actual Euclidean spaces. -/
theorem finite_expectation_bound [Nonempty ι] [Nonempty κ]
    (x : ι → EuclideanSpace ℝ α) (y : κ → EuclideanSpace ℝ β)
    (hx : ∀ i, ‖x i‖ = 1) (hy : ∀ j, ‖y j‖ = 1) :
    (∫ g, finiteMaximum (columnVectorValues y g) ∂coordinateGaussian (Source α β)) -
      (∫ g, finiteMaximum (rowVectorValues x g) ∂coordinateGaussian (Source α β)) ≤
        ∫ g, finiteMinMax (matrixValues x y g) ∂coordinateGaussian (Source α β) := by
  simpa only [integral_vectorProcess, integral_matrixProcess] using!
    finite_process_comparison x y hx hy

end ConvexBodyChasing.Gordon

end
end BundledModule097

/- Component source: ConvexBodyChasing.GordonOperators -/
section BundledModule098
/-! # The Gaussian matrix as a continuous linear operator

The matrix and vector coordinates from the finite Gordon inequality are
bundled as Euclidean random vectors and an operator-valued Gaussian linear map.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace
namespace ConvexBodyChasing.Gordon

variable {α β ι κ : Type*} [Fintype α] [Fintype β] [Fintype ι] [Fintype κ]

def rowGaussian : (Source α β → ℝ) →L[ℝ] EuclideanSpace ℝ α :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : α => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun a => ContinuousLinearMap.proj (.inr (.inr a))))

def columnGaussian : (Source α β → ℝ) →L[ℝ] EuclideanSpace ℝ β :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : β => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun b => ContinuousLinearMap.proj (.inr (.inl b))))

def matrixOperator : (Source α β → ℝ) →L[ℝ] (EuclideanSpace ℝ α →L[ℝ] EuclideanSpace ℝ β) := by
  classical
  exact ∑ a, ∑ b, (ContinuousLinearMap.proj (.inl (.inl (a, b)))).smulRight
    ((PiLp.proj 2 (fun _ : α => ℝ) a).smulRight (EuclideanSpace.single b 1))

omit [Fintype β] in
theorem rowGaussian_apply (g : Source α β → ℝ) (a : α) :
    rowGaussian g a = g (.inr (.inr a)) := rfl

omit [Fintype α] in
theorem columnGaussian_apply (g : Source α β → ℝ) (b : β) :
    columnGaussian g b = g (.inr (.inl b)) := rfl

theorem matrixOperator_apply (g : Source α β → ℝ) (x : EuclideanSpace ℝ α) (b : β) :
    matrixOperator g x b = ∑ a, g (.inl (.inl (a, b))) * x a := by
  classical
  simp [matrixOperator, Pi.single_apply]

omit [Fintype ι] [Fintype β] in
theorem rowVectorValues_eq_inner (x : ι → EuclideanSpace ℝ α) (g : Source α β → ℝ) (i : ι) :
    rowVectorValues x g i = ⟪rowGaussian g, x i⟫_ℝ := by
  rw [← sum_mul_coordinates]
  simp [rowVectorValues, rowGaussian_apply, mul_comm]

omit [Fintype κ] [Fintype α] in
theorem columnVectorValues_eq_inner (y : κ → EuclideanSpace ℝ β) (g : Source α β → ℝ) (j : κ) :
    columnVectorValues y g j = ⟪columnGaussian g, y j⟫_ℝ := by
  rw [← sum_mul_coordinates]
  simp [columnVectorValues, columnGaussian_apply, mul_comm]

omit [Fintype ι] [Fintype κ] in
theorem matrixValues_eq_inner (x : ι → EuclideanSpace ℝ α) (y : κ → EuclideanSpace ℝ β)
    (g : Source α β → ℝ) (a : ι × κ) :
    matrixValues x y g a = ⟪matrixOperator g (x a.1), y a.2⟫_ℝ := by
  rw [← sum_mul_coordinates]
  simp only [matrixOperator_apply, Finset.sum_mul, matrixValues, ContinuousLinearMap.pi_apply,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  simp only [mul_assoc, mul_comm]



theorem integrable_norm_columnGaussian : Integrable (fun g : Source α β → ℝ => ‖columnGaussian g‖)
    (coordinateGaussian (Source α β)) :=
  (((columnGaussian (α := α) (β := β)).comp_memLp'
    (coordinateGaussian_memLp_id (Source α β))).integrable (by norm_num)).norm

theorem integrable_norm_matrixOperator : Integrable (fun g : Source α β → ℝ => ‖matrixOperator g‖)
    (coordinateGaussian (Source α β)) :=
  (((matrixOperator (α := α) (β := β)).comp_memLp'
    (coordinateGaussian_memLp_id (Source α β))).integrable (by norm_num)).norm

end ConvexBodyChasing.Gordon

end
end BundledModule098

/- Component source: ConvexBodyChasing.GaussianMarginals -/
section BundledModule099
/-! # Gaussian coordinate marginals

Selecting distinct coordinates preserves the corresponding standard Gaussian
product law. This identifies the row vector used in Gordon comparison with
the Gaussian in the dual-width integral.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open MeasureTheory ProbabilityTheory
namespace ConvexBodyChasing

theorem coordinateGaussian_select_preserving {α β : Type*} [Fintype α] [Fintype β]
    {f : β → α} (hf : Function.Injective f) :
    MeasurePreserving (fun g : α → ℝ => g ∘ f) (coordinateGaussian α)
      (coordinateGaussian β) := by
  refine ⟨measurable_pi_lambda _ (fun b => measurable_pi_apply (f b)), ?_⟩
  have h := (iIndepFun_iff_map_fun_eq_pi_map
    (fun b : β => (measurable_pi_apply (f b)).aemeasurable)).mp
    ((coordinateGaussian_independent α).precomp hf)
  exact h.trans (congrArg Measure.pi (funext (fun i => (coordinateGaussian_eval α (f i)).map_eq)))

end ConvexBodyChasing

end
end BundledModule099

/- Component source: ConvexBodyChasing.GaussianDualWidth -/
section BundledModule100
/-! # The actual dual Gaussian width

The dual Gaussian is the transpose of a map into Euclidean space applied to
the standard Gaussian. Coordinate marginals identify it with the row Gaussian
in the Gordon probability space.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace ConvexBodyChasing

variable {E α β : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Fintype α] [Fintype β]

def euclideanDualOperator (J : E →L[ℝ] EuclideanSpace ℝ α) :
    EuclideanSpace ℝ α →L[ℝ] (E →L[ℝ] ℝ) :=
  ((ContinuousLinearMap.compL ℝ E (EuclideanSpace ℝ α) ℝ).flip J).comp (innerSL ℝ)

def gaussianDualOperator (J : E →L[ℝ] EuclideanSpace ℝ α) :
    (α → ℝ) →L[ℝ] (E →L[ℝ] ℝ) :=
  (euclideanDualOperator J).comp
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : α => ℝ)).symm.toContinuousLinearMap

def gaussianDualMean (J : E →L[ℝ] EuclideanSpace ℝ α) : ℝ :=
  ∫ g, ‖gaussianDualOperator J g‖ ∂coordinateGaussian α



theorem integrable_norm_gaussianDualOperator (J : E →L[ℝ] EuclideanSpace ℝ α) :
    Integrable (fun g => ‖gaussianDualOperator J g‖) (coordinateGaussian α) :=
  (((gaussianDualOperator J).comp_memLp' (coordinateGaussian_memLp_id α)).integrable
    (by norm_num)).norm

theorem gaussianDualMean_nonneg (J : E →L[ℝ] EuclideanSpace ℝ α) :
    0 ≤ gaussianDualMean J := integral_nonneg (fun _ => norm_nonneg _)

@[simp] theorem gaussianDualMean_zero : gaussianDualMean (0 : E →L[ℝ] EuclideanSpace ℝ α) = 0 := by
  simp [gaussianDualMean, gaussianDualOperator, euclideanDualOperator]

theorem gaussianDualMean_pos_of_ne_zero (J : E →L[ℝ] EuclideanSpace ℝ α) (hJ : J ≠ 0) :
    0 < gaussianDualMean J := by
  obtain ⟨x, hx⟩ := DFunLike.ne_iff.mp hJ
  apply integral_pos_of_integrable_nonneg_nonzero (x := fun a => J x a)
    (gaussianDualOperator J).continuous.norm (integrable_norm_gaussianDualOperator J)
    (fun _ => norm_nonneg _)
  intro h
  exact hx (inner_self_eq_zero.mp
    (show ⟪J x, J x⟫_ℝ = 0 from congrArg (fun L : E →L[ℝ] ℝ => L x) (norm_eq_zero.mp h)))

theorem integral_norm_rowGaussian_dual (J : E →L[ℝ] EuclideanSpace ℝ α) :
    (∫ g : Gordon.Source α β → ℝ, ‖euclideanDualOperator J (Gordon.rowGaussian g)‖
      ∂coordinateGaussian (Gordon.Source α β)) = gaussianDualMean J := by
  have hp := coordinateGaussian_select_preserving
    (show Function.Injective (fun a : α => (Sum.inr (Sum.inr a) : Gordon.Source α β))
      from Sum.inr_injective.comp Sum.inr_injective)
  exact hp.hasLaw.integral_comp (gaussianDualOperator J).continuous.norm.aestronglyMeasurable

end ConvexBodyChasing

end
end BundledModule100

/- Component source: ConvexBodyChasing.GaussianMeanBounds -/
section BundledModule101
/-! # From Gaussian L² bounds to mean widths

The means used by the low-M* theorem are bounded by the actual L² norms in
the MM* theorem. This module records the integral comparison with its moment
hypothesis discharged for continuous linear Gaussian images.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open MeasureTheory
namespace ConvexBodyChasing

theorem integral_norm_le_lpNorm_two {Ω F : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup F] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : Ω → F} (hf : MemLp f 2 μ) : (∫ x, ‖f x‖ ∂μ) ≤ lpNorm f 2 μ := by
  rw [← lpNorm_one_eq_integral_norm hf.aestronglyMeasurable,
    ← toReal_eLpNorm hf.aestronglyMeasurable, ← toReal_eLpNorm hf.aestronglyMeasurable]
  exact ENNReal.toReal_mono hf.eLpNorm_ne_top
    (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num) hf.aestronglyMeasurable)

theorem integral_norm_le_norm_toLp_two {Ω F : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup F] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : Ω → F} (hf : MemLp f 2 μ) : (∫ x, ‖f x‖ ∂μ) ≤ ‖hf.toLp f‖ := by
  simpa only [Lp.norm_toLp, toReal_eLpNorm hf.aestronglyMeasurable] using!
    integral_norm_le_lpNorm_two hf

theorem integral_norm_matrixOperatorEquiv_le {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (b : Module.Basis ι ℝ E) (T : Matrix ι ι ℝ) :
    (∫ g, ‖matrixOperatorEquiv b T g‖ ∂coordinateGaussian ι) ≤ gaussianMatrixNorm b T := by
  rw [gaussianMatrixNorm_eq_lpNorm]
  exact integral_norm_le_lpNorm_two
    ((matrixOperatorEquiv b T).comp_memLp' (coordinateGaussian_memLp_id ι))

theorem integral_norm_matrixRowFunctional_le {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (b : Module.Basis ι ℝ E) (B : Matrix ι ι ℝ) :
    (∫ g, ‖gaussianColumnOperator ι (matrixRowFunctional ι b B) g‖ ∂coordinateGaussian ι) ≤
      gaussianRowDualNorm b B :=
  integral_norm_le_norm_toLp_two (gaussianColumnOperator_memLp ι (matrixRowFunctional ι b B))

end ConvexBodyChasing

end
end BundledModule101

/- Component source: ConvexBodyChasing.EuclideanPosition -/
section BundledModule102
/-! # The Euclidean coordinates of the Gaussian MM* position

An invertible optimizing matrix gives mutually inverse continuous linear maps.
The inverse rows are identified with the dual Gaussian appearing in low-M*.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open MeasureTheory Module
open scoped BigOperators InnerProductSpace
namespace ConvexBodyChasing

variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

def matrixEuclideanMap (b : Basis ι ℝ E) (T : Matrix ι ι ℝ) :
    EuclideanSpace ℝ ι →L[ℝ] E :=
  (matrixOperatorEquiv b T).comp
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)).toContinuousLinearMap

def matrixEuclideanCoordinates (b : Basis ι ℝ E) (B : Matrix ι ι ℝ) :
    E →L[ℝ] EuclideanSpace ℝ ι :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (matrixRowFunctional ι b B))

omit [DecidableEq ι] in
theorem matrixEuclideanCoordinates_apply (b : Basis ι ℝ E) (B : Matrix ι ι ℝ)
    (x : E) (i : ι) : matrixEuclideanCoordinates b B x i = matrixRowFunctional ι b B i x := rfl

theorem matrixEuclideanCoordinates_matrixEuclideanMap (b : Basis ι ℝ E)
    (B T : Matrix ι ι ℝ) (y : EuclideanSpace ℝ ι) :
    matrixEuclideanCoordinates b B (matrixEuclideanMap b T y) =
      WithLp.toLp 2 ((B * T).mulVec y) := by
  ext i
  exact matrixRowFunctional_matrixOperatorEquiv b B T i y

theorem matrixEuclideanCoordinates_leftInverse (b : Basis ι ℝ E)
    (T : Matrix ι ι ℝ) (hT : T.det ≠ 0) :
    Function.LeftInverse (matrixEuclideanCoordinates b T⁻¹) (matrixEuclideanMap b T) := by
  intro y
  simp only [matrixEuclideanCoordinates_matrixEuclideanMap,
    Matrix.nonsing_inv_mul T (isUnit_iff_ne_zero.mpr hT), Matrix.one_mulVec, WithLp.toLp_ofLp]

theorem matrixEuclideanCoordinates_rightInverse (b : Basis ι ℝ E)
    (T : Matrix ι ι ℝ) (hT : T.det ≠ 0) :
    Function.RightInverse (matrixEuclideanCoordinates b T⁻¹) (matrixEuclideanMap b T) := by
  intro x
  apply b.equivFun.injective
  change b.equivFun (matrixOperatorEquiv b T (fun i => matrixRowFunctional ι b T⁻¹ i x)) =
    b.equivFun x
  simp only [equivFun_matrixOperatorEquiv, matrixRowFunctional_apply]
  change T.mulVec (T⁻¹.mulVec (b.equivFun x)) = b.equivFun x
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv T (isUnit_iff_ne_zero.mpr hT), Matrix.one_mulVec]

def matrixEuclideanEquiv (b : Basis ι ℝ E) (T : Matrix ι ι ℝ) (hT : T.det ≠ 0) :
    EuclideanSpace ℝ ι ≃L[ℝ] E :=
  ContinuousLinearEquiv.equivOfInverse (matrixEuclideanMap b T) (matrixEuclideanCoordinates b T⁻¹)
    (matrixEuclideanCoordinates_leftInverse b T hT) (matrixEuclideanCoordinates_rightInverse b T hT)

omit [DecidableEq ι] in
theorem gaussianDualOperator_matrixEuclideanCoordinates (b : Basis ι ℝ E) (B : Matrix ι ι ℝ) :
    gaussianDualOperator (matrixEuclideanCoordinates b B) =
      gaussianColumnOperator ι (matrixRowFunctional ι b B) := by
  ext g x
  change ⟪WithLp.toLp 2 g, matrixEuclideanCoordinates b B x⟫_ℝ =
    (gaussianColumnOperator ι (matrixRowFunctional ι b B) g) x
  simp only [← Gordon.sum_mul_coordinates, matrixEuclideanCoordinates_apply,
    gaussianColumnOperator_apply, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul]

omit [DecidableEq ι] in
theorem gaussianDualMean_matrixEuclideanCoordinates_le (b : Basis ι ℝ E) (B : Matrix ι ι ℝ) :
    gaussianDualMean (matrixEuclideanCoordinates b B) ≤ gaussianRowDualNorm b B := by
  simpa only [gaussianDualMean, gaussianDualOperator_matrixEuclideanCoordinates] using!
    integral_norm_matrixRowFunctional_le b B

def gaussianImageMean (L : EuclideanSpace ℝ ι →L[ℝ] E) : ℝ :=
  ∫ g : ι → ℝ, ‖L (WithLp.toLp 2 g)‖ ∂coordinateGaussian ι

/-- The Gaussian MM* position expressed as an actual Euclidean equivalence. -/
theorem exists_gaussian_MMstar_equiv [Nonempty ι] [FiniteDimensional ℝ E]
    (b : Basis ι ℝ E) {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (J : E →L[ℝ] H) {D : ℝ} (hD : 1 ≤ D)
    (hJ : ∀ x, ‖J x‖ ≤ ‖x‖) (hE : ∀ x, ‖x‖ ≤ D * ‖J x‖) :
    ∃ e : EuclideanSpace ℝ ι ≃L[ℝ] E,
      gaussianImageMean e.toContinuousLinearMap ≤ 1 ∧
      gaussianDualMean e.symm.toContinuousLinearMap ≤ 6 * (Fintype.card ι : ℝ) * Real.sqrt D := by
  obtain ⟨T, hT, hd, ht⟩ := exists_gaussian_MMstar_position b J hD hJ hE
  exact ⟨matrixEuclideanEquiv b T hd.ne', (integral_norm_matrixOperatorEquiv_le b T).trans_eq hT,
    (gaussianDualMean_matrixEuclideanCoordinates_le b T⁻¹).trans ht⟩

end ConvexBodyChasing

end
end BundledModule102

/- Component source: ConvexBodyChasing.GaussianOrthogonalImages -/
section BundledModule103
/-! # Orthogonal images and Gaussian mean contraction

Euclidean isometries preserve the standard Gaussian. An orthogonal projection
is the average of the identity and a reflection, so it decreases the Gaussian
mean of every normed linear image.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open MeasureTheory
open scoped InnerProductSpace BigOperators
namespace ConvexBodyChasing
variable {ι : Type*} [Fintype ι]

theorem coordinateGaussian_isometry_preserving
    (U : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι) :
    MeasurePreserving (fun g : ι → ℝ => (U (WithLp.toLp 2 g)).ofLp)
      (coordinateGaussian ι) (coordinateGaussian ι) := by
  classical
  refine ⟨((PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)).continuous.comp
    (U.continuous.comp (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)).symm.continuous)).measurable, ?_⟩
  let A : ι → ι → ℝ := fun i => (U.symm (EuclideanSpace.single i 1)).ofLp
  have hA (g : ι → ℝ) (i : ι) : (∑ k, A i k * g k) = U (WithLp.toLp 2 g) i := by
    change (∑ k, U.symm (EuclideanSpace.single i 1) k * (WithLp.toLp 2 g) k) = _
    simp only [Gordon.sum_mul_coordinates, LinearIsometryEquiv.inner_map_eq_flip,
      LinearIsometryEquiv.symm_symm, EuclideanSpace.inner_single_left, conj_trivial, one_mul]
  have horth : ∀ i j, i ≠ j → ∑ k, A i k * A j k = 0 := by
    intro i j hij
    simp [A, Gordon.sum_mul_coordinates, LinearIsometryEquiv.inner_map_map,
      EuclideanSpace.inner_single_left, hij]
  have hnorm : ∀ i, ∑ k, A i k ^ 2 = 1 := by
    intro i
    simp [A, pow_two, Gordon.sum_mul_coordinates]
  simpa only [hA] using! coordinateGaussian_map_orthonormal ι A horth hnorm

theorem integrable_norm_gaussianImage {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : EuclideanSpace ℝ ι →L[ℝ] E) :
    Integrable (fun g : ι → ℝ => ‖L (WithLp.toLp 2 g)‖) (coordinateGaussian ι) :=
  (((L.comp (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)).symm.toContinuousLinearMap).comp_memLp'
    (coordinateGaussian_memLp_id ι)).integrable (by norm_num)).norm

theorem gaussianImageMean_comp_isometry {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : EuclideanSpace ℝ ι →L[ℝ] E)
    (U : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι) :
    gaussianImageMean (L.comp U.toContinuousLinearEquiv.toContinuousLinearMap) =
      gaussianImageMean L := by
  exact (coordinateGaussian_isometry_preserving U).hasLaw.integral_comp
    (L.continuous.comp (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)).symm.continuous).norm.aestronglyMeasurable

theorem two_mul_norm_comp_starProjection_le {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : EuclideanSpace ℝ ι →L[ℝ] E) (V : Submodule ℝ (EuclideanSpace ℝ ι))
    (x : EuclideanSpace ℝ ι) :
    2 * ‖L (V.starProjection x)‖ ≤ ‖L x‖ + ‖L (V.reflection x)‖ := by
  have he : L x + L (V.reflection x) = (2 : ℝ) • L (V.starProjection x) := by
    simp [Submodule.reflection_apply, two_smul]
  simpa only [he, norm_smul, Real.norm_ofNat] using! norm_add_le (L x) (L (V.reflection x))

/-- Projecting a standard Gaussian onto a subspace decreases every norm mean. -/
theorem gaussianImageMean_comp_starProjection_le {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : EuclideanSpace ℝ ι →L[ℝ] E) (V : Submodule ℝ (EuclideanSpace ℝ ι)) :
    gaussianImageMean (L.comp V.starProjection) ≤ gaussianImageMean L := by
  have h := integral_mono ((integrable_norm_gaussianImage (L.comp V.starProjection)).const_mul 2)
    ((integrable_norm_gaussianImage L).add
      (integrable_norm_gaussianImage (L.comp V.reflection.toContinuousLinearEquiv.toContinuousLinearMap)))
    (fun g => two_mul_norm_comp_starProjection_le L V (WithLp.toLp 2 g))
  simp only [Pi.add_apply, integral_const_mul, integral_add (integrable_norm_gaussianImage L)
    (integrable_norm_gaussianImage (L.comp V.reflection.toContinuousLinearEquiv.toContinuousLinearMap))] at h
  change 2 * gaussianImageMean (L.comp V.starProjection) ≤ gaussianImageMean L +
    gaussianImageMean (L.comp V.reflection.toContinuousLinearEquiv.toContinuousLinearMap) at h
  rw [gaussianImageMean_comp_isometry] at h
  linarith

end ConvexBodyChasing

end
end BundledModule103

/- Component source: ConvexBodyChasing.QuotientGeometry -/
section BundledModule104
/-! # Geometry of the quotient lifting in the all-norms extension

These lemmas prove the elementary lifting step from the two unit-ball inclusions.
They do not assert the existence of a Milman quotient.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace ConvexBodyChasing

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The first unit-ball inclusion gives a norm-controlled lift of every vector. -/
theorem exists_lift_norm_le (Q : E →L[ℝ] F)
    (hball : Metric.closedBall 0 1 ⊆ Q '' Metric.closedBall 0 1) (y : F) :
    ∃ x : E, Q x = y ∧ ‖x‖ ≤ ‖y‖ := by
  by_cases hy : y = 0
  · subst y
    exact ⟨0, Q.map_zero, by simp⟩
  · obtain ⟨x, hx, hQx⟩ := hball (show ‖y‖⁻¹ • y ∈ Metric.closedBall 0 1 by
      simp [Metric.mem_closedBall, norm_smul, hy])
    refine ⟨‖y‖ • x, by simp [hQx, smul_smul, hy], ?_⟩
    simpa only [norm_smul, Real.norm_of_nonneg (norm_nonneg y), mul_one] using!
      mul_le_mul_of_nonneg_left (show ‖x‖ ≤ 1 by simpa using! hx) (norm_nonneg y)







/-- The second unit-ball inclusion bounds the cost of projection. -/
theorem norm_map_le_of_ball_image_subset (Q : E →L[ℝ] F) {M : ℝ} (hM : 0 ≤ M)
    (hball : Q '' Metric.closedBall 0 1 ⊆ Metric.closedBall 0 M) (x : E) :
    ‖Q x‖ ≤ M * ‖x‖ := by
  exact Q.le_of_opNorm_le (ContinuousLinearMap.opNorm_le_of_unit_norm hM
    (fun z hz => by simpa using! hball ⟨z, by simp [hz], rfl⟩)) x











end ConvexBodyChasing

end
end BundledModule104

/- Component source: ConvexBodyChasing.QuotientDuality -/
section BundledModule105
/-! # Dual norm estimates and quotient ball inclusions

The geometric QS proof can construct a quotient through its dual map. These
lemmas turn dual norm control into the exact closed-ball inclusion needed by
the chasing reduction, using compactness and Hahn–Banach separation.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace ConvexBodyChasing

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [ProperSpace E]

/-- An expanding dual map makes the image of the closed unit ball cover the target ball. -/
theorem closedBall_subset_image_of_dual_norm_le (Q : E →L[ℝ] F)
    (hdual : ∀ f : F →L[ℝ] ℝ, ‖f‖ ≤ ‖f.comp Q‖) :
    Metric.closedBall 0 1 ⊆ Q '' Metric.closedBall 0 1 := by
  intro y hy
  by_contra hnot
  obtain ⟨f, u, hbound, hfy⟩ := geometric_hahn_banach_closed_point
    ((convex_closedBall (0 : E) 1).linear_image Q.toLinearMap)
    (((isCompact_closedBall (0 : E) 1).image Q.continuous).isClosed) hnot
  have hu : 0 ≤ u := le_of_lt (by simpa using! hbound (Q 0) ⟨0, by simp, rfl⟩)
  have hnorm : ‖f.comp Q‖ ≤ u := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm hu
    intro x hx
    change |f (Q x)| ≤ u
    exact abs_le.mpr ⟨by
      simpa only [map_neg, neg_neg] using!
        neg_le_neg (hbound (Q (-x)) ⟨-x, by simp [hx], rfl⟩).le,
      (hbound (Q x) ⟨x, by simp [hx], rfl⟩).le⟩
  have hvalue : f y ≤ ‖f‖ := (le_abs_self _).trans ((f.le_opNorm y).trans
    (mul_le_of_le_one_right (norm_nonneg f) (by simpa using! hy)))
  exact hfy.not_ge (hvalue.trans ((hdual f).trans hnorm))





omit [ProperSpace E] in
/-- The upper dual norm estimate also gives the upper norm estimate for the original map. -/
theorem norm_map_le_of_dual_norm_bound (Q : E →L[ℝ] F) {M : ℝ} (hM : 0 ≤ M)
    (hdual : ∀ f : F →L[ℝ] ℝ, ‖f.comp Q‖ ≤ M * ‖f‖) (x : E) :
    ‖Q x‖ ≤ M * ‖x‖ := by
  exact NormedSpace.norm_le_dual_bound ℝ (Q x) (mul_nonneg hM (norm_nonneg x))
    (fun f => (((f.comp Q).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right (hdual f) (norm_nonneg x))).trans_eq
        (mul_right_comm M ‖f‖ ‖x‖))

section HilbertTarget

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Transpose a map into the dual, identifying the Hilbert target with its own dual. -/
def quotientOfDualMap (T : H →L[ℝ] (E →L[ℝ] ℝ)) : E →L[ℝ] H :=
  (InnerProductSpace.toDual ℝ H).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp T.flip

omit [ProperSpace E] in
theorem inner_quotientOfDualMap (T : H →L[ℝ] (E →L[ℝ] ℝ)) (x : E) (y : H) :
    inner ℝ (quotientOfDualMap T x) y = T y x := by
  exact InnerProductSpace.toDual_symm_apply

omit [ProperSpace E] in
theorem comp_quotientOfDualMap (T : H →L[ℝ] (E →L[ℝ] ℝ)) (f : H →L[ℝ] ℝ) :
    f.comp (quotientOfDualMap T) = T ((InnerProductSpace.toDual ℝ H).symm f) := by
  ext x
  exact (InnerProductSpace.toDual_symm_apply.symm.trans (real_inner_comm _ _)).trans
    (inner_quotientOfDualMap T x _)

/-- A lower estimate on a Hilbert-space embedding into the dual gives exact ball coverage. -/
theorem closedBall_subset_image_quotientOfDualMap (T : H →L[ℝ] (E →L[ℝ] ℝ))
    (hlower : ∀ y, ‖y‖ ≤ ‖T y‖) :
    Metric.closedBall 0 1 ⊆ quotientOfDualMap T '' Metric.closedBall 0 1 := by
  apply closedBall_subset_image_of_dual_norm_le
  exact fun f => by
    simpa only [comp_quotientOfDualMap, LinearIsometryEquiv.norm_map] using!
      hlower ((InnerProductSpace.toDual ℝ H).symm f)

omit [ProperSpace E] in
/-- An upper estimate on the dual embedding controls the projected movement. -/
theorem norm_quotientOfDualMap_le (T : H →L[ℝ] (E →L[ℝ] ℝ))
    {M : ℝ} (hM : 0 ≤ M) (hupper : ∀ y, ‖T y‖ ≤ M * ‖y‖) (x : E) :
    ‖quotientOfDualMap T x‖ ≤ M * ‖x‖ := by
  apply norm_map_le_of_dual_norm_bound _ hM
  exact fun f => by
    simpa only [comp_quotientOfDualMap, LinearIsometryEquiv.norm_map] using!
      hupper ((InnerProductSpace.toDual ℝ H).symm f)

/-- A Euclidean dual embedding supplies both ball inclusions in the QS formulation. -/
theorem quotient_ball_inclusions_of_dual_embedding (T : H →L[ℝ] (E →L[ℝ] ℝ))
    {M : ℝ} (hM : 0 ≤ M) (hlower : ∀ y, ‖y‖ ≤ ‖T y‖)
    (hupper : ∀ y, ‖T y‖ ≤ M * ‖y‖) :
    Metric.closedBall 0 1 ⊆ quotientOfDualMap T '' Metric.closedBall 0 1 ∧
      quotientOfDualMap T '' Metric.closedBall 0 1 ⊆ Metric.closedBall 0 M := by
  refine ⟨closedBall_subset_image_quotientOfDualMap T hlower, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  simpa only [Metric.mem_closedBall, dist_zero_right] using!
    (norm_quotientOfDualMap_le T hM hupper x).trans
      (mul_le_of_le_one_right hM (by simpa using! hx))

end HilbertTarget

end ConvexBodyChasing

end
end BundledModule105

/- Component source: ConvexBodyChasing.EuclideanTranspose -/
section BundledModule106
/-! # Euclidean transposes and their Gaussian widths

The transpose of a map from Euclidean space into a normed space is defined
using the canonical double-dual embedding. Its dual Gaussian width is bounded
by the original map's Gaussian norm mean.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace ConvexBodyChasing

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]

def euclideanTranspose (L : EuclideanSpace ℝ ι →L[ℝ] E) :
    (E →L[ℝ] ℝ) →L[ℝ] EuclideanSpace ℝ ι :=
  quotientOfDualMap ((NormedSpace.inclusionInDoubleDual ℝ E).comp L)

theorem inner_euclideanTranspose (L : EuclideanSpace ℝ ι →L[ℝ] E)
    (f : E →L[ℝ] ℝ) (z : EuclideanSpace ℝ ι) :
    ⟪euclideanTranspose L f, z⟫_ℝ = f (L z) :=
  inner_quotientOfDualMap ((NormedSpace.inclusionInDoubleDual ℝ E).comp L) f z

theorem euclideanDualOperator_transpose (L : EuclideanSpace ℝ ι →L[ℝ] E)
    (z : EuclideanSpace ℝ ι) :
    euclideanDualOperator (euclideanTranspose L) z = NormedSpace.inclusionInDoubleDual ℝ E (L z) := by
  ext f
  exact (real_inner_comm z (euclideanTranspose L f)).symm.trans (inner_euclideanTranspose L f z)

theorem gaussianDualMean_transpose_le (L : EuclideanSpace ℝ ι →L[ℝ] E) :
    gaussianDualMean (euclideanTranspose L) ≤ gaussianImageMean L := by
  apply integral_mono (integrable_norm_gaussianDualOperator (euclideanTranspose L))
    (integrable_norm_gaussianImage L)
  intro g
  change ‖euclideanDualOperator (euclideanTranspose L) (WithLp.toLp 2 g)‖ ≤ ‖L (WithLp.toLp 2 g)‖
  simpa only [euclideanDualOperator_transpose] using!
    NormedSpace.double_dual_bound (𝕜 := ℝ) E (L (WithLp.toLp 2 g))

theorem norm_le_mul_norm_euclideanTranspose (L : EuclideanSpace ℝ ι →L[ℝ] E)
    (J : E →L[ℝ] EuclideanSpace ℝ ι) (hLJ : Function.LeftInverse L J)
    {a : ℝ} (ha : 0 ≤ a) (hJ : ∀ x, ‖J x‖ ≤ a * ‖x‖) (f : E →L[ℝ] ℝ) :
    ‖f‖ ≤ a * ‖euclideanTranspose L f‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg ha (norm_nonneg _))
  intro x
  have he : ⟪euclideanTranspose L f, J x⟫_ℝ = f x :=
    (inner_euclideanTranspose L f (J x)).trans (congrArg f (hLJ x))
  simpa only [he, mul_left_comm, mul_assoc] using!
    (norm_inner_le_norm (𝕜 := ℝ) (euclideanTranspose L f) (J x)).trans
      (mul_le_mul_of_nonneg_left (hJ x) (norm_nonneg (euclideanTranspose L f)))

end ConvexBodyChasing

end
end BundledModule106

/- Component source: ConvexBodyChasing.FiniteNets -/
section BundledModule107
/-! # Finite nets and extrema estimates

Compact sets admit finite nets inside the set. A finite net of the unit
sphere approximates a vector norm through its inner products.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped InnerProductSpace
namespace ConvexBodyChasing

theorem exists_nonempty_finite_norm_net {E : Type*} [NormedAddCommGroup E]
    {S : Set E} (hS : IsCompact S) (hSne : S.Nonempty) {ε : ℝ} (hε : 0 < ε) :
    ∃ t : Set E, t ⊆ S ∧ t.Finite ∧ t.Nonempty ∧
      ∀ v ∈ S, ∃ w ∈ t, ‖v - w‖ < ε := by
  obtain ⟨t, htS, htf, htcover⟩ := hS.finite_cover_balls hε
  have hcover : ∀ v ∈ S, ∃ w ∈ t, ‖v - w‖ < ε := by
    intro v hv
    rcases Set.mem_iUnion.mp (htcover hv) with ⟨w, hw⟩
    rcases Set.mem_iUnion.mp hw with ⟨hwt, hdist⟩
    exact ⟨w, hwt, by simpa only [Metric.mem_ball, dist_eq_norm] using! hdist⟩
  refine ⟨t, htS, htf, ?_, hcover⟩
  obtain ⟨v, hv⟩ := hSne
  obtain ⟨w, hw, _⟩ := hcover v hv
  exact ⟨w, hw⟩

theorem norm_le_finiteMaximum_inner_add {E κ : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [Fintype κ] [Nonempty κ] (y : κ → E) {ε : ℝ}
    (hnet : ∀ u : E, ‖u‖ = 1 → ∃ j, ‖u - y j‖ ≤ ε) (z : E) :
    ‖z‖ ≤ finiteMaximum (fun j => ⟪z, y j⟫_ℝ) + ‖z‖ * ε := by
  by_cases hz : z = 0
  · simp [hz, finiteMaximum]
  let u : E := ‖z‖⁻¹ • z
  have hu : ‖u‖ = 1 := norm_smul_inv_norm hz
  obtain ⟨j, hj⟩ := hnet u hu
  have hzu : ⟪z, u⟫_ℝ = ‖z‖ := by
    simp [u, inner_smul_right, pow_two, norm_ne_zero_iff.mpr hz]
  have he : ⟪z, u - y j⟫_ℝ ≤ ‖z‖ * ε :=
    (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hj (norm_nonneg z))
  have hm : ⟪z, y j⟫_ℝ ≤ finiteMaximum (fun j => ⟪z, y j⟫_ℝ) :=
    Finset.le_sup' (fun j => ⟪z, y j⟫_ℝ) (Finset.mem_univ j)
  rw [inner_sub_right, hzu] at he
  linarith

theorem finiteMinMax_inner_le_of_near_kernel {E F ι κ : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [Fintype ι] [Fintype κ] [Nonempty ι] [Nonempty κ]
    (T : E →L[ℝ] F) (x : ι → E) (y : κ → F) (hy : ∀ j, ‖y j‖ ≤ 1)
    {v : E} (hv : T v = 0) {ε : ℝ} (hnear : ∃ i, ‖x i - v‖ ≤ ε) :
    finiteMinMax (fun a => ⟪T (x a.1), y a.2⟫_ℝ) ≤ ‖T‖ * ε := by
  obtain ⟨i, hi⟩ := hnear
  have hTi : ‖T (x i)‖ ≤ ‖T‖ * ε := by
    simpa only [map_sub, hv, sub_zero] using!
      (T.le_opNorm (x i - v)).trans (mul_le_mul_of_nonneg_left hi (norm_nonneg T))
  refine (finiteMinMax_le_finiteRowMax _ i).trans (Finset.sup'_le _ _ (fun j _ => ?_))
  exact ((real_inner_le_norm _ _).trans
    (mul_le_of_le_one_right (norm_nonneg _) (hy j))).trans hTi

end ConvexBodyChasing

end
end BundledModule107

/- Component source: ConvexBodyChasing.GordonEscape -/
section BundledModule108
/-! # Compact-set escape from finite Gordon comparison

Finite nets of the compact set and target unit sphere control the approximation
error by integrable Gaussian vector and matrix norms.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace ConvexBodyChasing.Gordon

variable {α β ι κ : Type*} [Fintype α] [Fintype β] [Fintype ι] [Fintype κ]

theorem integral_column_norm_le_finiteMaximum_add [Nonempty κ]
    (y : κ → EuclideanSpace ℝ β) {ε : ℝ}
    (hnet : ∀ u : EuclideanSpace ℝ β, ‖u‖ = 1 → ∃ j, ‖u - y j‖ ≤ ε) :
    (∫ g : Source α β → ℝ, ‖columnGaussian g‖ ∂coordinateGaussian (Source α β)) ≤
      (∫ g, finiteMaximum (columnVectorValues y g) ∂coordinateGaussian (Source α β)) +
        (∫ g : Source α β → ℝ, ‖columnGaussian g‖ ∂coordinateGaussian (Source α β)) * ε := by
  have hb (g : Source α β → ℝ) : ‖columnGaussian g‖ ≤
      finiteMaximum (columnVectorValues y g) + ‖columnGaussian g‖ * ε := by
    rw [show columnVectorValues y g = (fun j => ⟪columnGaussian g, y j⟫_ℝ)
      from funext (columnVectorValues_eq_inner y g)]
    exact norm_le_finiteMaximum_inner_add y hnet (columnGaussian g)
  have h := integral_mono (integrable_norm_columnGaussian (α := α) (β := β))
    ((integrable_gaussian_finiteMaximum (columnVectorValues (α := α) y)).add
      ((integrable_norm_columnGaussian (α := α) (β := β)).mul_const ε)) hb
  simpa only [Pi.add_apply, integral_add (integrable_gaussian_finiteMaximum (columnVectorValues (α := α) y))
    ((integrable_norm_columnGaussian (α := α) (β := β)).mul_const ε), integral_mul_const] using! h

theorem integral_row_maximum_le [Nonempty ι] (x : ι → EuclideanSpace ℝ α)
    {W : (Source α β → ℝ) → ℝ} (hWi : Integrable W (coordinateGaussian (Source α β)))
    (hW : ∀ g i, ⟪rowGaussian g, x i⟫_ℝ ≤ W g) :
    (∫ g, finiteMaximum (rowVectorValues x g) ∂coordinateGaussian (Source α β)) ≤
      ∫ g, W g ∂coordinateGaussian (Source α β) := by
  apply integral_mono (integrable_gaussian_finiteMaximum (rowVectorValues (β := β) x)) hWi
  intro g
  exact Finset.sup'_le _ _ (fun i _ => by simpa only [rowVectorValues_eq_inner] using! hW g i)

theorem integral_matrix_minMax_le_of_near_kernel [Nonempty ι] [Nonempty κ]
    (x : ι → EuclideanSpace ℝ α) (y : κ → EuclideanSpace ℝ β) (hy : ∀ j, ‖y j‖ ≤ 1)
    {ε : ℝ} (hkernel : ∀ g : Source α β → ℝ,
      ∃ v : EuclideanSpace ℝ α, matrixOperator g v = 0 ∧ ∃ i, ‖x i - v‖ ≤ ε) :
    (∫ g, finiteMinMax (matrixValues x y g) ∂coordinateGaussian (Source α β)) ≤
      (∫ g : Source α β → ℝ, ‖matrixOperator g‖ ∂coordinateGaussian (Source α β)) * ε := by
  have hb (g : Source α β → ℝ) : finiteMinMax (matrixValues x y g) ≤ ‖matrixOperator g‖ * ε := by
    obtain ⟨v, hv, hnear⟩ := hkernel g
    rw [show matrixValues x y g = (fun a => ⟪matrixOperator g (x a.1), y a.2⟫_ℝ)
      from funext (matrixValues_eq_inner x y g)]
    exact finiteMinMax_inner_le_of_near_kernel (matrixOperator g) x y hy hv hnear
  have h := integral_mono (integrable_gaussian_finiteMinMax_of_fintype (matrixValues x y))
    ((integrable_norm_matrixOperator (α := α) (β := β)).mul_const ε) hb
  simpa only [integral_mul_const] using! h

theorem integral_column_norm_le_width_add_net_error [Nonempty ι] [Nonempty κ]
    (x : ι → EuclideanSpace ℝ α) (y : κ → EuclideanSpace ℝ β)
    (hx : ∀ i, ‖x i‖ = 1) (hy : ∀ j, ‖y j‖ = 1) {ε : ℝ}
    (hnet : ∀ u : EuclideanSpace ℝ β, ‖u‖ = 1 → ∃ j, ‖u - y j‖ ≤ ε)
    (hkernel : ∀ g : Source α β → ℝ,
      ∃ v : EuclideanSpace ℝ α, matrixOperator g v = 0 ∧ ∃ i, ‖x i - v‖ ≤ ε)
    {W : (Source α β → ℝ) → ℝ} (hWi : Integrable W (coordinateGaussian (Source α β)))
    (hW : ∀ g i, ⟪rowGaussian g, x i⟫_ℝ ≤ W g) :
    (∫ g : Source α β → ℝ, ‖columnGaussian g‖ ∂coordinateGaussian (Source α β)) ≤
      (∫ g, W g ∂coordinateGaussian (Source α β)) +
        ((∫ g : Source α β → ℝ, ‖columnGaussian g‖ ∂coordinateGaussian (Source α β)) +
          ∫ g : Source α β → ℝ, ‖matrixOperator g‖ ∂coordinateGaussian (Source α β)) * ε := by
  have hc := integral_column_norm_le_finiteMaximum_add (α := α) y hnet
  have hr := integral_row_maximum_le x hWi hW
  have hm := integral_matrix_minMax_le_of_near_kernel x y (fun j => (hy j).le) hkernel
  have hg := finite_expectation_bound x y hx hy
  linarith

theorem integral_column_norm_le_width_add_compact_error [Nonempty β]
    {S : Set (EuclideanSpace ℝ α)} (hS : IsCompact S) (hSne : S.Nonempty)
    (hunit : ∀ v ∈ S, ‖v‖ = 1)
    (hkernel : ∀ g : Source α β → ℝ, ∃ v ∈ S, matrixOperator g v = 0)
    {W : (Source α β → ℝ) → ℝ} (hWi : Integrable W (coordinateGaussian (Source α β)))
    (hW : ∀ g v, v ∈ S → ⟪rowGaussian g, v⟫_ℝ ≤ W g)
    {ε : ℝ} (hε : 0 < ε) :
    (∫ g : Source α β → ℝ, ‖columnGaussian g‖ ∂coordinateGaussian (Source α β)) ≤
      (∫ g, W g ∂coordinateGaussian (Source α β)) +
        ((∫ g : Source α β → ℝ, ‖columnGaussian g‖ ∂coordinateGaussian (Source α β)) +
          ∫ g : Source α β → ℝ, ‖matrixOperator g‖ ∂coordinateGaussian (Source α β)) * ε := by
  classical
  obtain ⟨tx, htxS, htxf, htxne, htxnet⟩ := exists_nonempty_finite_norm_net hS hSne hε
  obtain ⟨ty, htyS, htyf, htyne, htynet⟩ := exists_nonempty_finite_norm_net
    (isCompact_sphere (0 : EuclideanSpace ℝ β) 1) (NormedSpace.sphere_nonempty.mpr zero_le_one) hε
  letI : Fintype tx := htxf.fintype
  letI : Fintype ty := htyf.fintype
  letI : Nonempty tx := htxne.to_subtype
  letI : Nonempty ty := htyne.to_subtype
  refine integral_column_norm_le_width_add_net_error
    (fun i : tx => (i : EuclideanSpace ℝ α)) (fun j : ty => (j : EuclideanSpace ℝ β))
    ?_ ?_ ?_ ?_ hWi ?_
  · exact fun i => hunit i (htxS i.property)
  · intro j
    simpa only [Metric.mem_sphere, dist_zero_right] using! htyS j.property
  · intro u hu
    obtain ⟨w, hw, hdist⟩ := htynet u (by simpa only [Metric.mem_sphere, dist_zero_right] using! hu)
    exact ⟨⟨w, hw⟩, hdist.le⟩
  · intro g
    obtain ⟨v, hvS, hv⟩ := hkernel g
    obtain ⟨w, hw, hdist⟩ := htxnet v hvS
    exact ⟨v, hv, ⟨w, hw⟩, by simpa only [norm_sub_rev] using! hdist.le⟩
  · exact fun g i => hW g i (htxS i.property)

theorem integral_column_norm_le_width_of_kernel_meets [Nonempty β]
    {S : Set (EuclideanSpace ℝ α)} (hS : IsCompact S) (hSne : S.Nonempty)
    (hunit : ∀ v ∈ S, ‖v‖ = 1)
    (hkernel : ∀ g : Source α β → ℝ, ∃ v ∈ S, matrixOperator g v = 0)
    {W : (Source α β → ℝ) → ℝ} (hWi : Integrable W (coordinateGaussian (Source α β)))
    (hW : ∀ g v, v ∈ S → ⟪rowGaussian g, v⟫_ℝ ≤ W g) :
    (∫ g : Source α β → ℝ, ‖columnGaussian g‖ ∂coordinateGaussian (Source α β)) ≤
      ∫ g, W g ∂coordinateGaussian (Source α β) := by
  let L := ∫ g : Source α β → ℝ, ‖columnGaussian g‖ ∂coordinateGaussian (Source α β)
  let w := ∫ g, W g ∂coordinateGaussian (Source α β)
  let K := L + ∫ g : Source α β → ℝ, ‖matrixOperator g‖ ∂coordinateGaussian (Source α β)
  change L ≤ w
  by_contra h
  let ε := (L - w) / (|K| + 1)
  have hε : 0 < ε := div_pos (sub_pos.mpr (lt_of_not_ge h)) (by positivity)
  have hb : L ≤ w + K * ε :=
    integral_column_norm_le_width_add_compact_error hS hSne hunit hkernel hWi hW hε
  have he : ε * (|K| + 1) = L - w := div_mul_cancel₀ _ (by positivity)
  have hs : K * ε < (|K| + 1) * ε :=
    mul_lt_mul_of_pos_right (by linarith [le_abs_self K]) hε
  nlinarith

/-- A compact subset of the unit sphere with sufficiently small Gaussian width
is avoided by the kernel of a linear map into the target Euclidean space. -/
theorem exists_kernel_avoiding_of_width_bound [Nonempty β]
    {S : Set (EuclideanSpace ℝ α)} (hS : IsCompact S) (hunit : ∀ v ∈ S, ‖v‖ = 1)
    {W : (Source α β → ℝ) → ℝ} (hWi : Integrable W (coordinateGaussian (Source α β)))
    (hW : ∀ g v, v ∈ S → ⟪rowGaussian g, v⟫_ℝ ≤ W g)
    (hwidth : (∫ g, W g ∂coordinateGaussian (Source α β)) <
      ∫ g : Source α β → ℝ, ‖columnGaussian g‖ ∂coordinateGaussian (Source α β)) :
    ∃ T : EuclideanSpace ℝ α →L[ℝ] EuclideanSpace ℝ β, ∀ v ∈ S, T v ≠ 0 := by
  classical
  by_contra h
  push_neg at h
  have hSne : S.Nonempty := by
    obtain ⟨v, hv, _⟩ := h 0
    exact ⟨v, hv⟩
  exact (not_le_of_gt hwidth)
    (integral_column_norm_le_width_of_kernel_meets hS hSne hunit
      (fun g => h (matrixOperator g)) hWi hW)

end ConvexBodyChasing.Gordon

end
end BundledModule108

/- Component source: ConvexBodyChasing.GaussianLength -/
section BundledModule109
/-! # A dimension-uniform lower bound on Gaussian Euclidean length

The positive absolute first moment of one standard Gaussian is an absolute
constant. Cauchy–Schwarz on coordinates gives the required square-root dimension
lower bound without any asymptotic or unproved moment estimate.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ConvexBodyChasing

def gaussianAbsoluteMean : ℝ := ∫ g : Unit → ℝ, |g ()| ∂coordinateGaussian Unit

theorem gaussianAbsoluteMean_pos : 0 < gaussianAbsoluteMean := by
  apply integral_pos_of_integrable_nonneg_nonzero (x := fun _ : Unit => (1 : ℝ))
    (continuous_apply ()).abs
    ((((coordinateGaussian_memLp_id Unit).eval ()).integrable (by norm_num)).abs)
    (fun g => abs_nonneg (g ()))
  norm_num

theorem integral_abs_coordinateGaussian {ι : Type*} [Fintype ι] (i : ι) :
    (∫ g : ι → ℝ, |g i| ∂coordinateGaussian ι) = gaussianAbsoluteMean := by
  exact ((coordinateGaussian_eval ι i).hasLaw.integral_comp
    continuous_abs.aestronglyMeasurable).trans
    ((coordinateGaussian_eval Unit ()).hasLaw.integral_comp
      continuous_abs.aestronglyMeasurable).symm

theorem sum_abs_le_sqrt_card_mul_norm {ι : Type*} [Fintype ι]
    (z : EuclideanSpace ℝ ι) :
    (∑ i, |z i|) ≤ Real.sqrt (Fintype.card ι) * ‖z‖ := by
  simpa [EuclideanSpace.norm_eq, Real.norm_eq_abs] using!
    Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun _ : ι => (1 : ℝ)) (fun i => |z i|)

theorem integral_norm_columnGaussian_lower {α β : Type*} [Fintype α] [Fintype β] :
    gaussianAbsoluteMean * Real.sqrt (Fintype.card β) ≤
      ∫ g : Gordon.Source α β → ℝ, ‖Gordon.columnGaussian g‖
        ∂coordinateGaussian (Gordon.Source α β) := by
  have hi (b : β) : Integrable (fun g : Gordon.Source α β → ℝ => |g (.inr (.inl b))|)
      (coordinateGaussian (Gordon.Source α β)) := by
    simpa only [id_eq] using!
      (((coordinateGaussian_memLp_id (Gordon.Source α β)).eval (.inr (.inl b))).integrable
        (by norm_num)).abs
  have hb := integral_mono (integrable_finset_sum Finset.univ (fun b _ => hi b))
    ((Gordon.integrable_norm_columnGaussian (α := α) (β := β)).const_mul
      (Real.sqrt (Fintype.card β)))
    (fun g => sum_abs_le_sqrt_card_mul_norm (Gordon.columnGaussian g))
  simp only [integral_finset_sum Finset.univ (fun b _ => hi b),
    integral_abs_coordinateGaussian, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    integral_const_mul] at hb
  by_cases hc : Fintype.card β = 0
  · simpa [hc] using! integral_nonneg
      (fun g : Gordon.Source α β → ℝ => norm_nonneg (Gordon.columnGaussian g))
  · have hs : 0 < Real.sqrt (Fintype.card β) :=
      Real.sqrt_pos.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hc))
    apply (mul_le_mul_iff_right₀ hs).mp
    nlinarith only [hb, congrArg (fun t : ℝ => t * gaussianAbsoluteMean)
      (Real.sq_sqrt (Nat.cast_nonneg (Fintype.card β)))]

end ConvexBodyChasing

end
end BundledModule109

/- Component source: ConvexBodyChasing.LowMStar -/
section BundledModule110
/-! # A low-M* section estimate

Kernel escape applied to the image of a norm ball gives a subspace on which
the Euclidean norm is bounded. The width is the actual Gaussian dual norm
integral, and the dimension loss follows from rank-nullity.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace ConvexBodyChasing

variable {E α β : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Fintype α] [Fintype β]

theorem norm_le_mul_of_kernel_avoids_ball_image
    (J : E →L[ℝ] EuclideanSpace ℝ α)
    (T : EuclideanSpace ℝ α →L[ℝ] EuclideanSpace ℝ β)
    {r : ℝ} (hr : 0 < r)
    (hT : ∀ v ∈ J '' Metric.closedBall 0 r⁻¹ ∩ Metric.sphere 0 1, T v ≠ 0)
    {x : E} (hx : T (J x) = 0) : ‖J x‖ ≤ r * ‖x‖ := by
  by_contra h
  have hn : 0 < ‖J x‖ := lt_of_le_of_lt (mul_nonneg hr.le (norm_nonneg x)) (lt_of_not_ge h)
  let y := ‖J x‖⁻¹ • x
  have hy : ‖y‖ ≤ r⁻¹ := by
    simpa [y, norm_smul, abs_of_pos (inv_pos.mpr hn), mul_comm, div_eq_mul_inv] using!
      ((div_lt_div_iff₀ hn hr).mpr (by nlinarith : ‖x‖ * r < 1 * ‖J x‖)).le
  have hu : ‖J y‖ = 1 := by
    simpa only [y, map_smul] using! norm_smul_inv_norm (norm_pos_iff.mp hn)
  exact hT (J y) ⟨⟨y, by simpa only [Metric.mem_closedBall, dist_zero_right] using! hy, rfl⟩,
    by simpa only [Metric.mem_sphere, dist_zero_right] using! hu⟩ (by simp [y, hx])

/-- The quantitative section is a kernel of a map to the specified target. -/
theorem exists_lowMStar_kernel [FiniteDimensional ℝ E] [Nonempty β]
    (J : E →L[ℝ] EuclideanSpace ℝ α) {r : ℝ} (hr : 0 < r)
    (hwidth : gaussianDualMean J < gaussianAbsoluteMean * Real.sqrt (Fintype.card β) * r) :
    ∃ T : E →L[ℝ] EuclideanSpace ℝ β, ∀ x, T x = 0 → ‖J x‖ ≤ r * ‖x‖ := by
  let S := J '' Metric.closedBall 0 r⁻¹ ∩ Metric.sphere 0 1
  have hS : IsCompact S :=
    ((isCompact_closedBall (0 : E) r⁻¹).image J.continuous).inter_right Metric.isClosed_sphere
  let D : (Gordon.Source α β → ℝ) →L[ℝ] (E →L[ℝ] ℝ) :=
    (euclideanDualOperator J).comp Gordon.rowGaussian
  have hDi : Integrable (fun g => ‖D g‖) (coordinateGaussian (Gordon.Source α β)) :=
    ((D.comp_memLp' (coordinateGaussian_memLp_id (Gordon.Source α β))).integrable
      (by norm_num)).norm
  have hsupp : ∀ g v, v ∈ S → ⟪Gordon.rowGaussian g, v⟫_ℝ ≤ ‖D g‖ / r := by
    rintro g v ⟨⟨x, hx, rfl⟩, _⟩
    exact (le_abs_self (D g x)).trans (((D g).le_opNorm x).trans (by
      simpa only [div_eq_mul_inv] using! mul_le_mul_of_nonneg_left
        (show ‖x‖ ≤ r⁻¹ by simpa only [Metric.mem_closedBall, dist_zero_right] using! hx)
        (norm_nonneg (D g))))
  have hw : (∫ g, ‖D g‖ / r ∂coordinateGaussian (Gordon.Source α β)) <
      ∫ g : Gordon.Source α β → ℝ, ‖Gordon.columnGaussian g‖
        ∂coordinateGaussian (Gordon.Source α β) := by
    rw [integral_div, show (∫ g, ‖D g‖ ∂coordinateGaussian (Gordon.Source α β)) =
      gaussianDualMean J from integral_norm_rowGaussian_dual J]
    exact ((div_lt_iff₀ hr).mpr hwidth).trans_le integral_norm_columnGaussian_lower
  obtain ⟨T, hT⟩ := Gordon.exists_kernel_avoiding_of_width_bound hS
    (fun v hv => by simpa only [Metric.mem_sphere, dist_zero_right] using! hv.2)
    (hDi.div_const r) hsupp hw
  exact ⟨T.comp J, fun _ hx => norm_le_mul_of_kernel_avoids_ball_image J T hr hT hx⟩

/-- A section loses at most `m` dimensions and has the stated Euclidean radius bound. -/
theorem exists_lowMStar_subspace [FiniteDimensional ℝ E]
    (J : E →L[ℝ] EuclideanSpace ℝ α) {m : ℕ} (hm : 0 < m)
    {r : ℝ} (hr : 0 < r)
    (hwidth : gaussianDualMean J < gaussianAbsoluteMean * Real.sqrt m * r) :
    ∃ V : Submodule ℝ E, Module.finrank ℝ E ≤ Module.finrank ℝ V + m ∧
      ∀ x ∈ V, ‖J x‖ ≤ r * ‖x‖ := by
  letI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  obtain ⟨T, hT⟩ := exists_lowMStar_kernel (β := Fin m) J hr (by simpa using! hwidth)
  refine ⟨T.toLinearMap.ker, ?_, fun x hx => hT x hx⟩
  have hdim := T.toLinearMap.finrank_range_add_finrank_ker
  have hrange : Module.finrank ℝ T.toLinearMap.range ≤ m := by
    simpa using! T.toLinearMap.range.finrank_le
  omega

/-- The low-M* estimate with an explicit absolute constant and no width hypothesis. -/
theorem lowMStar [FiniteDimensional ℝ E]
    (J : E →L[ℝ] EuclideanSpace ℝ α) {m : ℕ} (hm : 0 < m) :
    ∃ V : Submodule ℝ E, Module.finrank ℝ E ≤ Module.finrank ℝ V + m ∧
      ∀ x ∈ V, ‖J x‖ ≤
        (2 * gaussianDualMean J / (gaussianAbsoluteMean * Real.sqrt m)) * ‖x‖ := by
  by_cases hJ : J = 0
  · simpa [hJ] using!
      (show ∃ V : Submodule ℝ E, Module.finrank ℝ E ≤ Module.finrank ℝ V + m from
        ⟨⊤, by simp⟩)
  · have hc : 0 < gaussianAbsoluteMean * Real.sqrt m :=
      mul_pos gaussianAbsoluteMean_pos (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hm))
    have hμ := gaussianDualMean_pos_of_ne_zero J hJ
    apply exists_lowMStar_subspace J hm (div_pos (mul_pos (by norm_num) hμ) hc)
    simpa only [mul_div_cancel₀ _ hc.ne'] using! (show gaussianDualMean J < 2 * gaussianDualMean J by
      linarith)

end ConvexBodyChasing

end
end BundledModule110

/- Component source: ConvexBodyChasing.SubspaceGaussian -/
section BundledModule111
/-! # Gaussian widths after restriction to a subspace

An ambient Euclidean equivalence gives coordinates on a normed subspace.
Orthogonal projection followed by that equivalence has Gaussian mean no
larger than the ambient mean. Its transpose is the coordinate map on the dual.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open MeasureTheory
namespace ConvexBodyChasing

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]

def subspaceGaussianProjection (e : EuclideanSpace ℝ ι ≃L[ℝ] E) (V : Submodule ℝ E) :
    EuclideanSpace ℝ ι →L[ℝ] V :=
  (e.symm.submoduleMap V).symm.toContinuousLinearMap.comp
    (V.map e.symm.toLinearMap).orthogonalProjection

theorem coe_subspaceGaussianProjection (e : EuclideanSpace ℝ ι ≃L[ℝ] E)
    (V : Submodule ℝ E) (z : EuclideanSpace ℝ ι) :
    (subspaceGaussianProjection e V z : E) = e ((V.map e.symm.toLinearMap).starProjection z) :=
  ContinuousLinearEquiv.submoduleMap_symm_apply e.symm V _

theorem subspaceGaussianProjection_inverse (e : EuclideanSpace ℝ ι ≃L[ℝ] E)
    (V : Submodule ℝ E) (x : V) : subspaceGaussianProjection e V (e.symm x) = x := by
  change (e.symm.submoduleMap V).symm ((V.map e.symm.toLinearMap).orthogonalProjection
    (e.symm x)) = x
  rw [← ContinuousLinearEquiv.submoduleMap_apply e.symm V x,
    Submodule.orthogonalProjection_mem_subspace_eq_self, ContinuousLinearEquiv.symm_apply_apply]

theorem gaussianImageMean_subspaceGaussianProjection_le (e : EuclideanSpace ℝ ι ≃L[ℝ] E)
    (V : Submodule ℝ E) : gaussianImageMean (subspaceGaussianProjection e V) ≤
      gaussianImageMean e.toContinuousLinearMap := by
  have he : gaussianImageMean (subspaceGaussianProjection e V) =
      gaussianImageMean (e.toContinuousLinearMap.comp (V.map e.symm.toLinearMap).starProjection) := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun g =>
      congrArg norm (coe_subspaceGaussianProjection e V (WithLp.toLp 2 g)))
  exact he.trans_le (gaussianImageMean_comp_starProjection_le e.toContinuousLinearMap _)

def subspaceDualCoordinates (e : EuclideanSpace ℝ ι ≃L[ℝ] E) (V : Submodule ℝ E) :
    (V →L[ℝ] ℝ) →L[ℝ] EuclideanSpace ℝ ι := euclideanTranspose (subspaceGaussianProjection e V)

theorem gaussianDualMean_subspaceDualCoordinates_le (e : EuclideanSpace ℝ ι ≃L[ℝ] E)
    (V : Submodule ℝ E) : gaussianDualMean (E := V →L[ℝ] ℝ) (subspaceDualCoordinates e V) ≤
      gaussianImageMean e.toContinuousLinearMap :=
  (gaussianDualMean_transpose_le (subspaceGaussianProjection e V)).trans
    (gaussianImageMean_subspaceGaussianProjection_le e V)

theorem norm_le_mul_norm_subspaceDualCoordinates (e : EuclideanSpace ℝ ι ≃L[ℝ] E)
    (V : Submodule ℝ E) {a : ℝ} (ha : 0 ≤ a)
    (hV : ∀ x ∈ V, ‖e.symm x‖ ≤ a * ‖x‖) (f : V →L[ℝ] ℝ) :
    ‖f‖ ≤ a * ‖subspaceDualCoordinates e V f‖ :=
  norm_le_mul_norm_euclideanTranspose (subspaceGaussianProjection e V)
    (e.symm.toContinuousLinearMap.comp V.subtypeL) (subspaceGaussianProjection_inverse e V)
    ha (fun x => hV x x.property) f

open scoped InnerProductSpace in
theorem inner_subspaceDualCoordinates (e : EuclideanSpace ℝ ι ≃L[ℝ] E)
    (V : Submodule ℝ E) (f : V →L[ℝ] ℝ) (x : V) :
    ⟪subspaceDualCoordinates e V f, e.symm x⟫_ℝ = f x :=
  (inner_euclideanTranspose (subspaceGaussianProjection e V) f (e.symm x)).trans
    (congrArg f (subspaceGaussianProjection_inverse e V x))

theorem subspaceDualCoordinates_injective (e : EuclideanSpace ℝ ι ≃L[ℝ] E)
    (V : Submodule ℝ E) : Function.Injective (subspaceDualCoordinates e V) := by
  intro f g hfg
  ext x
  rw [← inner_subspaceDualCoordinates e V f x, hfg, inner_subspaceDualCoordinates]

/-- A second low-M* application controls the Euclidean and dual norms on a large subspace. -/
theorem exists_subspace_dual_section [FiniteDimensional ℝ E]
    (e : EuclideanSpace ℝ ι ≃L[ℝ] E) (V : Submodule ℝ E) {a : ℝ} (ha : 0 ≤ a)
    (hV : ∀ x ∈ V, ‖e.symm x‖ ≤ a * ‖x‖) {m : ℕ} (hm : 0 < m) :
    ∃ U : Submodule ℝ (V →L[ℝ] ℝ), Module.finrank ℝ V ≤ Module.finrank ℝ U + m ∧
      ∀ f ∈ U,
        ‖subspaceDualCoordinates e V f‖ ≤
          (2 * gaussianImageMean e.toContinuousLinearMap / (gaussianAbsoluteMean * Real.sqrt m)) * ‖f‖ ∧
        ‖f‖ ≤ a * ‖subspaceDualCoordinates e V f‖ := by
  obtain ⟨U, hd, hU⟩ := lowMStar (E := V →L[ℝ] ℝ) (subspaceDualCoordinates e V) hm
  have he : Module.finrank ℝ (V →L[ℝ] ℝ) = Module.finrank ℝ V :=
    (LinearMap.toContinuousLinearMap : (V →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (V →L[ℝ] ℝ)).symm.finrank_eq.trans
      Subspace.dual_finrank_eq
  refine ⟨U, he ▸ hd, fun f hf => ⟨?_, norm_le_mul_norm_subspaceDualCoordinates e V ha hV f⟩⟩
  exact (hU f hf).trans (mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
      (gaussianDualMean_subspaceDualCoordinates_le e V) (by norm_num))
      (mul_nonneg gaussianAbsoluteMean_pos.le (Real.sqrt_nonneg _))) (norm_nonneg f))

end ConvexBodyChasing

end
end BundledModule111

/- Component source: ConvexBodyChasing.DualSectionQuotient -/
section BundledModule112
/-! # A Euclidean quotient from a section of the dual

Two-sided norm bounds on an injective Euclidean coordinate map yield an
actual quotient with the same dimension and explicit closed-ball inclusions.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace ConvexBodyChasing

theorem exists_quotient_of_dual_coordinates {E H : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    (U : Submodule ℝ (E →L[ℝ] ℝ)) (A : (E →L[ℝ] ℝ) →L[ℝ] H) (hA : Function.Injective A)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hcoord : ∀ f ∈ U, ‖A f‖ ≤ b * ‖f‖) (hdual : ∀ f ∈ U, ‖f‖ ≤ a * ‖A f‖) :
    ∃ F : Submodule ℝ H, Module.finrank ℝ F = Module.finrank ℝ U ∧
      ∃ Q : E →L[ℝ] F,
        Metric.closedBall 0 1 ⊆ Q '' Metric.closedBall 0 1 ∧
        Q '' Metric.closedBall 0 1 ⊆ Metric.closedBall 0 (a * b) := by
  let B := A.comp U.subtypeL
  have hB : Function.Injective B := hA.comp Subtype.val_injective
  let k : U ≃L[ℝ] B.range :=
    (LinearEquiv.ofInjective B.toLinearMap hB).toContinuousLinearEquiv (𝕜 := ℝ) (E := U)
      (F := B.range)
  let T : B.range →L[ℝ] (E →L[ℝ] ℝ) := b • (U.subtypeL.comp k.symm.toContinuousLinearMap)
  have hk (y : B.range) : A (k.symm y) = (y : H) := congrArg Subtype.val (k.apply_symm_apply y)
  have hTnorm (y : B.range) : ‖T y‖ = b * ‖(k.symm y : E →L[ℝ] ℝ)‖ := by
    simp only [T, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
      Submodule.subtypeL_apply, ContinuousLinearEquiv.coe_coe, norm_smul, Real.norm_of_nonneg hb]
  have hlower (y : B.range) : ‖y‖ ≤ ‖T y‖ := by
    simpa only [hTnorm, hk, Submodule.norm_coe] using! hcoord (k.symm y) (k.symm y).property
  have hupper (y : B.range) : ‖T y‖ ≤ (a * b) * ‖y‖ := by
    simpa only [hTnorm, hk, Submodule.norm_coe, mul_left_comm, mul_assoc] using!
      mul_le_mul_of_nonneg_left (hdual (k.symm y) (k.symm y).property) hb
  exact ⟨B.range, k.toLinearEquiv.finrank_eq.symm, quotientOfDualMap T,
    quotient_ball_inclusions_of_dual_embedding T (mul_nonneg ha hb) hlower hupper⟩

end ConvexBodyChasing

end
end BundledModule112

/- Component source: ConvexBodyChasing.QuantitativeQS -/
section BundledModule113
/-! # A quantitative quotient-of-a-subspace step

Two low-M* applications and the dual quotient construction give exact ball
inclusions while losing at most twice the chosen codimension. The Gaussian
MM* position supplies a sublinear dependence on the initial distortion.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open MeasureTheory
namespace ConvexBodyChasing

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_quotient_subspace_of_gaussian_means (e : EuclideanSpace ℝ ι ≃L[ℝ] E)
    {m : ℕ} (hm : 0 < m) :
    ∃ V : Submodule ℝ E, ∃ F : Submodule ℝ (EuclideanSpace ℝ ι),
      Module.finrank ℝ E ≤ Module.finrank ℝ F + 2 * m ∧
      ∃ Q : V →L[ℝ] F,
        Metric.closedBall 0 1 ⊆ Q '' Metric.closedBall 0 1 ∧
        Q '' Metric.closedBall 0 1 ⊆ Metric.closedBall 0
          ((2 * gaussianDualMean e.symm.toContinuousLinearMap /
              (gaussianAbsoluteMean * Real.sqrt m)) *
            (2 * gaussianImageMean e.toContinuousLinearMap /
              (gaussianAbsoluteMean * Real.sqrt m))) := by
  obtain ⟨V, hVdim, hV⟩ := lowMStar e.symm.toContinuousLinearMap hm
  have hc : 0 ≤ gaussianAbsoluteMean * Real.sqrt m :=
    mul_nonneg gaussianAbsoluteMean_pos.le (Real.sqrt_nonneg _)
  have ha : 0 ≤ 2 * gaussianDualMean e.symm.toContinuousLinearMap /
      (gaussianAbsoluteMean * Real.sqrt m) :=
    div_nonneg (mul_nonneg (by norm_num) (gaussianDualMean_nonneg _)) hc
  have hb : 0 ≤ 2 * gaussianImageMean e.toContinuousLinearMap /
      (gaussianAbsoluteMean * Real.sqrt m) :=
    div_nonneg (mul_nonneg (by norm_num) (integral_nonneg (fun _ => norm_nonneg _))) hc
  obtain ⟨U, hUdim, hU⟩ := exists_subspace_dual_section e V ha hV hm
  obtain ⟨F, hFdim, Q, hQi, hQo⟩ := exists_quotient_of_dual_coordinates U
    (subspaceDualCoordinates e V) (subspaceDualCoordinates_injective e V) ha hb
    (fun f hf => (hU f hf).1) (fun f hf => (hU f hf).2)
  exact ⟨V, F, by omega, Q, hQi, hQo⟩

theorem gaussian_QS_radius_eq (a b : ℝ) (m : ℕ) :
    (2 * a / (gaussianAbsoluteMean * Real.sqrt m)) *
      (2 * b / (gaussianAbsoluteMean * Real.sqrt m)) =
        4 * (a * b) / (gaussianAbsoluteMean ^ 2 * m) := by
  rw [div_mul_div_comm]
  congr 1
  · ring
  · nlinarith only [congrArg (fun t : ℝ => gaussianAbsoluteMean ^ 2 * t)
      (Real.sq_sqrt (Nat.cast_nonneg m))]

/-- A QS improvement with radius `24 n √D / (c² m)`, where `c = E|N(0,1)| > 0`. -/
theorem exists_quantitative_QS [DecidableEq ι] [Nonempty ι]
    (basis : Module.Basis ι ℝ E) {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (J : E →L[ℝ] H) {D : ℝ} (hD : 1 ≤ D)
    (hJ : ∀ x, ‖J x‖ ≤ ‖x‖) (hE : ∀ x, ‖x‖ ≤ D * ‖J x‖)
    {m : ℕ} (hm : 0 < m) :
    ∃ V : Submodule ℝ E, ∃ F : Submodule ℝ (EuclideanSpace ℝ ι),
      Module.finrank ℝ E ≤ Module.finrank ℝ F + 2 * m ∧
      ∃ Q : V →L[ℝ] F,
        Metric.closedBall 0 1 ⊆ Q '' Metric.closedBall 0 1 ∧
        Q '' Metric.closedBall 0 1 ⊆ Metric.closedBall 0
          (24 * (Fintype.card ι : ℝ) * Real.sqrt D / (gaussianAbsoluteMean ^ 2 * m)) := by
  obtain ⟨e, hp, hd⟩ := exists_gaussian_MMstar_equiv basis J hD hJ hE
  obtain ⟨V, F, hdim, Q, hQi, hQo⟩ := exists_quotient_subspace_of_gaussian_means e hm
  refine ⟨V, F, hdim, Q, hQi, hQo.trans (Metric.closedBall_subset_closedBall ?_)⟩
  have hprod : gaussianDualMean e.symm.toContinuousLinearMap * gaussianImageMean e.toContinuousLinearMap ≤
      6 * (Fintype.card ι : ℝ) * Real.sqrt D :=
    (mul_le_mul_of_nonneg_left hp (gaussianDualMean_nonneg _)).trans (by simpa only [mul_one] using! hd)
  rw [gaussian_QS_radius_eq]
  exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hprod (by norm_num))
    (mul_nonneg (sq_nonneg _) (Nat.cast_nonneg m))).trans_eq (by ring)

end ConvexBodyChasing

end
end BundledModule113

/- Component source: ConvexBodyChasing.NormedQuotient -/
section BundledModule114
/-! # Exact ball images for finite-dimensional normed quotients

The quotient norm attains its infimum in finite dimensions. Consequently the
canonical quotient sends every closed norm ball onto the corresponding ball.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace ConvexBodyChasing

attribute [local instance] Submodule.closed_of_finiteDimensional

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def normedQuotientMap (S : Submodule ℝ E) : E →L[ℝ] E ⧸ S :=
  S.mkQ.mkContinuous 1 (fun x => by simpa only [one_mul] using! Submodule.Quotient.norm_mk_le S x)

theorem normedQuotientMap_apply (S : Submodule ℝ E) (x : E) :
    normedQuotientMap S x = Submodule.Quotient.mk x := rfl

theorem quotient_exists_norm_eq [FiniteDimensional ℝ E] (S : Submodule ℝ E) (q : E ⧸ S) :
    ∃ x : E, normedQuotientMap S x = q ∧ ‖x‖ = ‖q‖ := by
  obtain ⟨x, rfl⟩ := S.mkQ_surjective q
  obtain ⟨y, hy, hd⟩ := S.closed_of_finiteDimensional.exists_infDist_eq_dist ⟨0, S.zero_mem⟩ x
  refine ⟨x - y, ?_, ?_⟩
  · simp only [map_sub, normedQuotientMap_apply, Submodule.mkQ_apply,
      (Submodule.Quotient.mk_eq_zero S).mpr hy, sub_zero]
  · exact (hd.trans (dist_eq_norm x y)).symm.trans
      (QuotientAddGroup.norm_mk (S := S.toAddSubgroup) x).symm

/-- Finite-dimensional quotient maps send closed balls onto closed balls, including
the boundary. No enlargement of the radius is needed. -/
theorem normedQuotientMap_image_closedBall [FiniteDimensional ℝ E]
    (S : Submodule ℝ E) (r : ℝ) :
    normedQuotientMap S '' Metric.closedBall 0 r = Metric.closedBall 0 r := by
  ext q
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa only [Metric.mem_closedBall, dist_zero_right, normedQuotientMap_apply] using!
      (Submodule.Quotient.norm_mk_le S x).trans (show ‖x‖ ≤ r by simpa using! hx)
  · intro hq
    obtain ⟨x, hx, hn⟩ := quotient_exists_norm_eq S q
    exact ⟨x, by simpa only [Metric.mem_closedBall, dist_zero_right, hn] using! hq, hx⟩

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The first isomorphism theorem, with the actual quotient norm on the source. -/
def normedQuotientEquiv [FiniteDimensional ℝ E] (Q : E →L[ℝ] F)
    (hQ : Function.Surjective Q) : (E ⧸ Q.ker) ≃L[ℝ] F :=
  (Q.toLinearMap.quotKerEquivOfSurjective hQ).toContinuousLinearEquiv

theorem normedQuotientEquiv_mk [FiniteDimensional ℝ E] (Q : E →L[ℝ] F)
    (hQ : Function.Surjective Q) (x : E) :
    normedQuotientEquiv Q hQ (normedQuotientMap Q.ker x) = Q x := rfl

theorem finrank_normedQuotient_eq [FiniteDimensional ℝ E] (Q : E →L[ℝ] F)
    (hQ : Function.Surjective Q) : Module.finrank ℝ (E ⧸ Q.ker) = Module.finrank ℝ F :=
  (normedQuotientEquiv Q hQ).toLinearEquiv.finrank_eq

/-- Ball coverage controls the inverse coordinate map without any loss. -/
theorem norm_le_normedQuotientEquiv [FiniteDimensional ℝ E] (Q : E →L[ℝ] F)
    (hQ : Function.Surjective Q)
    (hball : Metric.closedBall 0 1 ⊆ Q '' Metric.closedBall 0 1) (x : E ⧸ Q.ker) :
    ‖x‖ ≤ ‖normedQuotientEquiv Q hQ x‖ := by
  obtain ⟨y, hy, hn⟩ := exists_lift_norm_le Q hball (normedQuotientEquiv Q hQ x)
  have hx : normedQuotientMap Q.ker y = x :=
    (normedQuotientEquiv Q hQ).injective hy
  exact (congrArg norm hx).symm.le.trans ((Submodule.Quotient.norm_mk_le Q.ker y).trans hn)

/-- The image-ball bound controls the forward quotient coordinate map. -/
theorem normedQuotientEquiv_norm_le [FiniteDimensional ℝ E] (Q : E →L[ℝ] F)
    (hQ : Function.Surjective Q) {M : ℝ} (hM : 0 ≤ M)
    (hball : Q '' Metric.closedBall 0 1 ⊆ Metric.closedBall 0 M) (x : E ⧸ Q.ker) :
    ‖normedQuotientEquiv Q hQ x‖ ≤ M * ‖x‖ := by
  obtain ⟨y, rfl, hn⟩ := quotient_exists_norm_eq Q.ker x
  simpa only [normedQuotientEquiv_mk, hn] using! norm_map_le_of_ball_image_subset Q hM hball y

theorem normedQuotientEquiv_norm_eq [FiniteDimensional ℝ E] (Q : E →L[ℝ] F)
    (hQ : Function.Surjective Q)
    (hball : Q '' Metric.closedBall 0 1 = Metric.closedBall 0 1) (x : E ⧸ Q.ker) :
    ‖normedQuotientEquiv Q hQ x‖ = ‖x‖ := by
  exact le_antisymm
    (by simpa only [one_mul] using! normedQuotientEquiv_norm_le Q hQ zero_le_one hball.subset x)
    (norm_le_normedQuotientEquiv Q hQ hball.superset x)

/-- The normalized Hilbert comparison used by the next QS step is on the
normed quotient, not on the Euclidean target equipped with a different norm. -/
theorem exists_normedQuotient_comparison [FiniteDimensional ℝ E] (Q : E →L[ℝ] F)
    {M : ℝ} (hM : 0 < M)
    (hcover : Metric.closedBall 0 1 ⊆ Q '' Metric.closedBall 0 1)
    (hbound : Q '' Metric.closedBall 0 1 ⊆ Metric.closedBall 0 M) :
    ∃ J : (E ⧸ Q.ker) →L[ℝ] F,
      (∀ x, ‖J x‖ ≤ ‖x‖) ∧ (∀ x, ‖x‖ ≤ M * ‖J x‖) := by
  have hQ : Function.Surjective Q := fun y =>
    (exists_lift_norm_le Q hcover y).imp (fun _ h => h.1)
  refine ⟨M⁻¹ • (normedQuotientEquiv Q hQ).toContinuousLinearMap, ?_, ?_⟩
  · intro x
    simpa only [ContinuousLinearMap.smul_apply, ContinuousLinearEquiv.coe_coe, norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr hM.le), ← mul_assoc, inv_mul_cancel₀ hM.ne', one_mul]
      using! mul_le_mul_of_nonneg_left (normedQuotientEquiv_norm_le Q hQ hM.le hbound x)
        (inv_nonneg.mpr hM.le)
  · intro x
    simpa only [ContinuousLinearMap.smul_apply, ContinuousLinearEquiv.coe_coe, norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr hM.le), ← mul_assoc, mul_inv_cancel₀ hM.ne', one_mul]
      using! norm_le_normedQuotientEquiv Q hQ hcover x

end ConvexBodyChasing

end
end BundledModule114

/- Component source: ConvexBodyChasing.SubquotientComposition -/
section BundledModule115
/-! # Composition of normed quotients of subspaces

The exact image of the unit ball, rather than an accumulated distortion bound,
is preserved under composition. This is the geometric input for iterating QS.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace ConvexBodyChasing

variable {E F H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- A quotient of a subspace carrying its actual quotient norm. -/
structure NormedSubquotient (E F : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] where
  subspace : Submodule ℝ E
  map : subspace →L[ℝ] F
  image_unitBall : map '' Metric.closedBall 0 1 = Metric.closedBall 0 1

/-- Restrict a map to the inverse image of a subspace. -/
def subspacePreimageMap (Q : E →L[ℝ] F) (V : Submodule ℝ F) :
    V.comap Q.toLinearMap →L[ℝ] V :=
  (Q.comp (V.comap Q.toLinearMap).subtypeL).codRestrict V (fun x => x.property)



theorem subspacePreimageMap_image_closedBall (Q : E →L[ℝ] F) (V : Submodule ℝ F)
    (r : ℝ) (hQ : Q '' Metric.closedBall 0 r = Metric.closedBall 0 r) :
    subspacePreimageMap Q V '' Metric.closedBall 0 r = Metric.closedBall 0 r := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hQ.subset ⟨x, hx, rfl⟩
  · intro hy
    obtain ⟨x, hx, hxy⟩ := hQ.superset (show (y : F) ∈ Metric.closedBall 0 r from hy)
    exact ⟨⟨x, show Q x ∈ V from hxy ▸ y.property⟩, hx, Subtype.ext hxy⟩

/-- A subspace of a subspace has exactly the norm of its image in the ambient space. -/
def subspaceFlattenEquiv (V : Submodule ℝ E) (W : Submodule ℝ V) :
    W ≃ₗᵢ[ℝ] W.map V.subtype :=
  { V.equivSubtypeMap W with norm_map' _ := rfl }

theorem image_closedBall_comp (Q : E →L[ℝ] F) (T : F →L[ℝ] H) (r : ℝ)
    (hQ : Q '' Metric.closedBall 0 r = Metric.closedBall 0 r) :
    (T.comp Q) '' Metric.closedBall 0 r = T '' Metric.closedBall 0 r := by
  change (T ∘ Q) '' Metric.closedBall 0 r = T '' Metric.closedBall 0 r
  rw [Set.image_comp, hQ]

namespace NormedSubquotient

theorem surjective (q : NormedSubquotient E F) : Function.Surjective q.map :=
  fun y => (exists_lift_norm_le q.map q.image_unitBall.superset y).imp (fun _ h => h.1)





def refl (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] : NormedSubquotient E E where
  subspace := ⊤
  map := (⊤ : Submodule ℝ E).subtypeL
  image_unitBall := by
    ext x
    exact ⟨fun ⟨y, hy, he⟩ => he ▸ hy, fun hx => ⟨⟨x, trivial⟩, hx, rfl⟩⟩

theorem finrank_le [FiniteDimensional ℝ E] (q : NormedSubquotient E F) :
    Module.finrank ℝ F ≤ Module.finrank ℝ E :=
  (finrank_normedQuotient_eq q.map q.surjective).symm.le.trans
    ((Submodule.finrank_quotient_le q.map.ker).trans (Submodule.finrank_le q.subspace))

/-- The inverse-image subspace, flattened into the original ambient space. -/
def pullbackSubspace (q : NormedSubquotient E F) (V : Submodule ℝ F) : Submodule ℝ E :=
  (V.comap q.map.toLinearMap).map q.subspace.subtype

/-- The exact quotient onto a subspace of the first quotient. -/
def pullbackMap (q : NormedSubquotient E F) (V : Submodule ℝ F) :
    q.pullbackSubspace V →L[ℝ] V :=
  (subspacePreimageMap q.map V).comp
    (subspaceFlattenEquiv q.subspace (V.comap q.map.toLinearMap)).symm.toLinearIsometry.toContinuousLinearMap

theorem pullbackMap_image_unitBall (q : NormedSubquotient E F) (V : Submodule ℝ F) :
    q.pullbackMap V '' Metric.closedBall 0 1 = Metric.closedBall 0 1 := by
  rw [pullbackMap, image_closedBall_comp]
  · exact subspacePreimageMap_image_closedBall q.map V 1 q.image_unitBall
  · simpa only [LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry,
      map_zero] using!
      (subspaceFlattenEquiv q.subspace (V.comap q.map.toLinearMap)).symm.image_closedBall 0 1

/-- Compose exact normed subquotients without any multiplication of distortions. -/
def comp (q : NormedSubquotient E F) (t : NormedSubquotient F H) : NormedSubquotient E H where
  subspace := q.pullbackSubspace t.subspace
  map := t.map.comp (q.pullbackMap t.subspace)
  image_unitBall := (image_closedBall_comp _ _ 1 (q.pullbackMap_image_unitBall t.subspace)).trans
    t.image_unitBall



attribute [local instance] Submodule.closed_of_finiteDimensional

/-- The canonical finite-dimensional quotient is an exact normed subquotient. -/
def ofQuotient [FiniteDimensional ℝ E] (V : Submodule ℝ E) (S : Submodule ℝ V) :
    NormedSubquotient E (V ⧸ S) where
  subspace := V
  map := normedQuotientMap S
  image_unitBall := normedQuotientMap_image_closedBall S 1

/-- Re-express an exact subquotient as a canonical quotient of a subspace of the
original space, preserving dimension and both comparison bounds. -/
theorem exists_quotient_comparison [FiniteDimensional ℝ E] (q : NormedSubquotient E F)
    (J : F →L[ℝ] H) {D : ℝ} (hJ : ∀ x, ‖J x‖ ≤ ‖x‖)
    (hF : ∀ x, ‖x‖ ≤ D * ‖J x‖) :
    ∃ V : Submodule ℝ E, ∃ S : Submodule ℝ V,
      Module.finrank ℝ (V ⧸ S) = Module.finrank ℝ F ∧
      ∃ J' : (V ⧸ S) →L[ℝ] H,
        (∀ x, ‖J' x‖ ≤ ‖x‖) ∧ (∀ x, ‖x‖ ≤ D * ‖J' x‖) := by
  let e := normedQuotientEquiv q.map q.surjective
  have he (x : q.subspace ⧸ q.map.ker) : ‖e x‖ = ‖x‖ :=
    normedQuotientEquiv_norm_eq q.map q.surjective q.image_unitBall x
  refine ⟨q.subspace, q.map.ker, finrank_normedQuotient_eq q.map q.surjective,
    J.comp e.toContinuousLinearMap, ?_, ?_⟩
  · intro x
    simpa only [he] using! hJ (e x)
  · intro x
    simpa only [he] using! hF (e x)

end NormedSubquotient
end ConvexBodyChasing

end
end BundledModule115

/- Component source: ConvexBodyChasing.QuantitativeNormedQS -/
section BundledModule116
/-! # A QS step with the quotient norm retained

This version returns the actual normed quotient and a new Euclidean comparison.
Exact normed subquotients compose, so the comparison from a subsequent step does
not multiply the distortions of preceding steps.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace ConvexBodyChasing

attribute [local instance] Submodule.closed_of_finiteDimensional

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_quantitative_normed_QS (basis : Module.Basis ι ℝ E)
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (J : E →L[ℝ] H) {D : ℝ} (hD : 1 ≤ D)
    (hJ : ∀ x, ‖J x‖ ≤ ‖x‖) (hE : ∀ x, ‖x‖ ≤ D * ‖J x‖)
    {m : ℕ} (hm : 0 < m) :
    ∃ V : Submodule ℝ E, ∃ S : Submodule ℝ V,
      Module.finrank ℝ E ≤ Module.finrank ℝ (V ⧸ S) + 2 * m ∧
      ∃ J' : (V ⧸ S) →L[ℝ] EuclideanSpace ℝ ι,
        (∀ x, ‖J' x‖ ≤ ‖x‖) ∧
        (∀ x, ‖x‖ ≤
          (24 * (Fintype.card ι : ℝ) * Real.sqrt D / (gaussianAbsoluteMean ^ 2 * m)) * ‖J' x‖) := by
  obtain ⟨V, F, hdim, Q, hcover, hbound⟩ := exists_quantitative_QS basis J hD hJ hE hm
  have hM : 0 < 24 * (Fintype.card ι : ℝ) * Real.sqrt D / (gaussianAbsoluteMean ^ 2 * m) := by
    have hc := gaussianAbsoluteMean_pos
    have hn : 0 < (Fintype.card ι : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
    have hDp : 0 < D := lt_of_lt_of_le zero_lt_one hD
    positivity
  obtain ⟨J', hJ', hE'⟩ := exists_normedQuotient_comparison Q hM hcover hbound
  have hQ : Function.Surjective Q := fun y =>
    (exists_lift_norm_le Q hcover y).imp (fun _ h => h.1)
  refine ⟨V, Q.ker, ?_, F.subtypeL.comp J', hJ', hE'⟩
  simpa only [finrank_normedQuotient_eq Q hQ] using! hdim

end ConvexBodyChasing

end
end BundledModule116

/- Component source: ConvexBodyChasing.QSIterationParameters -/
section BundledModule117
/-! # Explicit parameters for the QS iteration

The codimension is rounded up with a natural-number quotient. The distortion
levels grow rapidly, allowing a bounded total dimension loss when the levels
are traversed in reverse. These are numerical lemmas, not the QS conclusion.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators
namespace ConvexBodyChasing

def qsIterationScale : ℝ := 256 * (24 / gaussianAbsoluteMean ^ 2) + 8

def qsDistortionLevel (r : ℕ) : ℝ :=
  (qsIterationScale * (2 : ℝ) ^ r * (2 : ℝ) ^ (2 ^ r)) ^ 2

def qsIterationCodimension (N r : ℕ) : ℕ := N / 2 ^ (r + 7) + 1

theorem qsIterationScale_ge_eight : 8 ≤ qsIterationScale := by
  unfold qsIterationScale
  linarith [show 0 ≤ 256 * (24 / gaussianAbsoluteMean ^ 2) by positivity]

theorem qsIterationCodimension_pos (N r : ℕ) : 0 < qsIterationCodimension N r :=
  Nat.zero_lt_succ _

theorem dimension_le_qsIterationCodimension_mul (N r : ℕ) :
    N ≤ qsIterationCodimension N r * 2 ^ (r + 7) := by
  simpa only [qsIterationCodimension, Nat.mul_comm] using!
    (Nat.lt_mul_div_succ N (by positivity : 0 < 2 ^ (r + 7))).le

theorem qsIterationScale_pos : 0 < qsIterationScale :=
  lt_of_lt_of_le (by norm_num) qsIterationScale_ge_eight

theorem sqrt_qsDistortionLevel (r : ℕ) :
    Real.sqrt (qsDistortionLevel r) = qsIterationScale * (2 : ℝ) ^ r * (2 : ℝ) ^ (2 ^ r) := by
  exact Real.sqrt_sq (mul_nonneg (mul_nonneg qsIterationScale_pos.le (by positivity)) (by positivity))

theorem qsDistortionLevel_lower (r : ℕ) : 64 * ((r : ℝ) + 1) ≤ qsDistortionLevel r := by
  have hp : 1 ≤ (2 : ℝ) ^ r := one_le_pow₀ (by norm_num)
  have hq : 1 ≤ (2 : ℝ) ^ (2 ^ r) := one_le_pow₀ (by norm_num)
  have hr : (r : ℝ) + 1 ≤ (2 : ℝ) ^ r := by exact_mod_cast Nat.succ_le_of_lt r.lt_two_pow_self
  have ha : 8 * (2 : ℝ) ^ r ≤ qsIterationScale * (2 : ℝ) ^ r * (2 : ℝ) ^ (2 ^ r) :=
    (mul_le_mul_of_nonneg_right qsIterationScale_ge_eight (by positivity)).trans
      (le_mul_of_one_le_right (mul_nonneg qsIterationScale_pos.le (by positivity)) hq)
  have hs := mul_self_le_mul_self (by positivity : 0 ≤ 8 * (2 : ℝ) ^ r) ha
  unfold qsDistortionLevel
  nlinarith [sq_nonneg ((2 : ℝ) ^ r - 1)]

theorem qsDistortionLevel_ge_one (r : ℕ) : 1 ≤ qsDistortionLevel r := by
  have h := qsDistortionLevel_lower r
  have hr : 0 ≤ (r : ℝ) := Nat.cast_nonneg r
  linarith

theorem dimension_le_initial_qsDistortionLevel (N : ℕ) : (N : ℝ) ≤ qsDistortionLevel (N / 64) := by
  have h : (N : ℝ) ≤ 64 * ((N / 64 : ℕ) + 1 : ℝ) := by
    exact_mod_cast (Nat.lt_mul_div_succ N (by norm_num : 0 < 64)).le
  exact h.trans (qsDistortionLevel_lower _)

theorem qsDistortionLevel_step (r : ℕ) :
    (24 / gaussianAbsoluteMean ^ 2) * (2 : ℝ) ^ (r + 7) *
      Real.sqrt (qsDistortionLevel (r + 1)) ≤ qsDistortionLevel r := by
  have hscale : 256 * (24 / gaussianAbsoluteMean ^ 2) ≤ qsIterationScale := by
    unfold qsIterationScale
    linarith
  have h := mul_le_mul_of_nonneg_right hscale
    (show 0 ≤ qsIterationScale * ((2 : ℝ) ^ r) ^ 2 * ((2 : ℝ) ^ (2 ^ r)) ^ 2 from
      mul_nonneg (mul_nonneg qsIterationScale_pos.le (sq_nonneg _)) (sq_nonneg _))
  rw [sqrt_qsDistortionLevel, qsDistortionLevel, pow_add, Nat.pow_succ, pow_succ, pow_mul]
  norm_num only [show (2 : ℝ) ^ 7 = 128 by norm_num]
  convert! h using 1 <;> ring

/-- The actual quantitative QS radius fits the preceding distortion level. -/
theorem quantitative_QS_radius_le_level {n N : ℕ} (hn : n ≤ N) (r : ℕ) :
    24 * (n : ℝ) * Real.sqrt (qsDistortionLevel (r + 1)) /
      (gaussianAbsoluteMean ^ 2 * qsIterationCodimension N r) ≤ qsDistortionLevel r := by
  have hm : 0 < (qsIterationCodimension N r : ℝ) :=
    Nat.cast_pos.mpr (qsIterationCodimension_pos N r)
  have hnm : (n : ℝ) ≤ (qsIterationCodimension N r : ℝ) * (2 : ℝ) ^ (r + 7) := by
    exact_mod_cast hn.trans (dimension_le_qsIterationCodimension_mul N r)
  have hratio : (n : ℝ) / qsIterationCodimension N r ≤ (2 : ℝ) ^ (r + 7) :=
    (div_le_iff₀ hm).mpr (by simpa only [mul_comm] using! hnm)
  calc
    _ = (24 / gaussianAbsoluteMean ^ 2) * ((n : ℝ) / qsIterationCodimension N r) *
        Real.sqrt (qsDistortionLevel (r + 1)) := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ ≤ (24 / gaussianAbsoluteMean ^ 2) * (2 : ℝ) ^ (r + 7) *
        Real.sqrt (qsDistortionLevel (r + 1)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hratio (by positivity))
        (Real.sqrt_nonneg _)
    _ ≤ _ := qsDistortionLevel_step r

theorem sum_qsIterationCodimension_le (N t : ℕ) :
    ∑ r ∈ Finset.range t, qsIterationCodimension N r ≤ 2 * (N / 128) + t := by
  have h := Nat.geom_sum_le (b := 2) (by norm_num) (N / 128) t
  simp only [qsIterationCodimension, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_range, smul_eq_mul, mul_one]
  suffices ∑ r ∈ Finset.range t, N / 2 ^ (r + 7) ≤ 2 * (N / 128) from Nat.add_le_add_right this t
  simpa only [Nat.add_comm, pow_add, Nat.div_div_eq_div_mul, show (2 : ℕ) ^ 7 = 128 by norm_num,
    show (2 : ℕ) - 1 = 1 by norm_num, Nat.div_one, Nat.mul_comm] using! h

def qsDimensionLoss (N t : ℕ) : ℕ :=
  2 * ∑ r ∈ Finset.range t, qsIterationCodimension N r

theorem qsDimensionLoss_zero (N : ℕ) : qsDimensionLoss N 0 = 0 := by
  simp only [qsDimensionLoss, Finset.sum_range_zero, mul_zero]

theorem qsDimensionLoss_succ (N t : ℕ) :
    qsDimensionLoss N (t + 1) = qsDimensionLoss N t + 2 * qsIterationCodimension N t := by
  simp only [qsDimensionLoss, Finset.sum_range_succ, mul_add]

theorem qsDimensionLoss_le (N t : ℕ) : qsDimensionLoss N t ≤ 4 * (N / 128) + 2 * t := by
  have h := Nat.mul_le_mul_left 2 (sum_qsIterationCodimension_le N t)
  simpa only [qsDimensionLoss, mul_add, ← mul_assoc] using! h

/-- The chosen iteration length leaves at least half the original dimension. -/
theorem twice_qsDimensionLoss_le (N : ℕ) : 2 * qsDimensionLoss N (N / 64) ≤ N := by
  have h := qsDimensionLoss_le N (N / 64)
  have h₁ := Nat.div_mul_le_self N 128
  have h₂ := Nat.div_mul_le_self N 64
  omega

end ConvexBodyChasing

end
end BundledModule117

/- Component source: ConvexBodyChasing.InitialEuclideanComparison -/
section BundledModule118
/-! # A dimension-controlled initial Euclidean comparison

Maximize the determinant on the operator-norm unit ball. The resulting trace
bound, tested on rank-one operators, bounds the inverse by the dimension.
This supplies the starting comparison for the QS iteration for every norm.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped Matrix.Norms.Elementwise InnerProductSpace
namespace ConvexBodyChasing

variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

def matrixEuclideanEmbedding (b : Module.Basis ι ℝ E) :
    Matrix ι ι ℝ →L[ℝ] (EuclideanSpace ℝ ι →L[ℝ] E) :=
  LinearMap.toContinuousLinearMap {
    toFun := matrixEuclideanMap b
    map_add' := fun A B => by simp only [matrixEuclideanMap, map_add, ContinuousLinearMap.add_comp]
    map_smul' := fun c A => by
      simp only [matrixEuclideanMap, map_smul, ContinuousLinearMap.smul_comp, RingHom.id_apply] }

theorem matrixEuclideanEmbedding_injective (b : Module.Basis ι ℝ E) :
    Function.Injective (matrixEuclideanEmbedding b) := by
  intro A B h
  apply (matrixOperatorEquiv b).injective
  ext y
  exact congrArg (fun L : EuclideanSpace ℝ ι →L[ℝ] E => L (WithLp.toLp 2 y)) h

theorem matrixEuclideanMap_vecMulVec (b : Module.Basis ι ℝ E) (x : E)
    (z : EuclideanSpace ℝ ι) :
    matrixEuclideanMap b (Matrix.vecMulVec (b.equivFun x) z) = InnerProductSpace.rankOne ℝ x z := by
  ext y
  apply b.equivFun.injective
  rw [InnerProductSpace.rankOne_apply, map_smul]
  change b.equivFun (matrixOperatorEquiv b _ y) = _
  rw [equivFun_matrixOperatorEquiv, Matrix.vecMulVec_mulVec]
  simp only [← Gordon.sum_mul_coordinates, dotProduct, op_smul_eq_smul]

omit [DecidableEq ι] in
theorem trace_mul_vecMulVec_coordinates (b : Module.Basis ι ℝ E) (B : Matrix ι ι ℝ)
    (x : E) (z : EuclideanSpace ℝ ι) :
    Matrix.trace (B * Matrix.vecMulVec (b.equivFun x) z) =
      ⟪matrixEuclideanCoordinates b B x, z⟫_ℝ := by
  rw [Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, ← Gordon.sum_mul_coordinates]
  simp only [Matrix.mulVec, dotProduct, matrixEuclideanCoordinates_apply, matrixRowFunctional_apply]

/-- The supporting trace functional controls the norm of the inverse coordinate map. -/
theorem norm_matrixEuclideanCoordinates_le_of_trace_bound (b : Module.Basis ι ℝ E)
    (B : Matrix ι ι ℝ) {C : ℝ} (hC : 0 ≤ C)
    (htrace : ∀ A, |Matrix.trace (B * A)| ≤ C * ‖matrixEuclideanMap b A‖) (x : E) :
    ‖matrixEuclideanCoordinates b B x‖ ≤ C * ‖x‖ := by
  have h := htrace (Matrix.vecMulVec (b.equivFun x) (matrixEuclideanCoordinates b B x))
  rw [trace_mul_vecMulVec_coordinates, real_inner_self_eq_norm_sq, abs_of_nonneg (sq_nonneg _),
    matrixEuclideanMap_vecMulVec, InnerProductSpace.norm_rankOne] at h
  by_cases hz : matrixEuclideanCoordinates b B x = 0
  · simpa only [hz, norm_zero] using! mul_nonneg hC (norm_nonneg x)
  · exact (mul_le_mul_iff_left₀ (norm_pos_iff.mpr hz)).mp
      (by simpa only [pow_two, ← mul_assoc] using! h)

/-- Every positive-dimensional norm has an initial Euclidean distortion at most its dimension. -/
theorem exists_initial_Euclidean_equiv [Nonempty ι] (b : Module.Basis ι ℝ E) :
    ∃ e : EuclideanSpace ℝ ι ≃L[ℝ] E,
      (∀ z, ‖e z‖ ≤ ‖z‖) ∧ (∀ x, ‖e.symm x‖ ≤ (Fintype.card ι : ℝ) * ‖x‖) := by
  obtain ⟨T, hT, hd, ht⟩ := exists_unit_norm_determinant_position
    (matrixEuclideanEmbedding b) (matrixEuclideanEmbedding_injective b)
  refine ⟨matrixEuclideanEquiv b T hd.ne', ?_, ?_⟩
  · intro z
    change ‖(matrixEuclideanEmbedding b T) z‖ ≤ ‖z‖
    simpa only [hT, one_mul] using! (matrixEuclideanEmbedding b T).le_opNorm z
  · exact norm_matrixEuclideanCoordinates_le_of_trace_bound b T⁻¹ (Nat.cast_nonneg _) ht

/-- The normalized form required by `exists_quantitative_QS`, with `D = dim E`. -/
theorem exists_initial_Hilbert_comparison [Nonempty ι] (b : Module.Basis ι ℝ E) :
    ∃ J : E →L[ℝ] EuclideanSpace ℝ ι,
      (∀ x, ‖J x‖ ≤ ‖x‖) ∧ (∀ x, ‖x‖ ≤ (Fintype.card ι : ℝ) * ‖J x‖) := by
  obtain ⟨e, he, hi⟩ := exists_initial_Euclidean_equiv b
  have hn : 0 < (Fintype.card ι : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  refine ⟨(Fintype.card ι : ℝ)⁻¹ • e.symm.toContinuousLinearMap, ?_, ?_⟩
  · intro x
    simpa only [ContinuousLinearMap.smul_apply, ContinuousLinearEquiv.coe_coe, norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr hn.le), ← mul_assoc, inv_mul_cancel₀ hn.ne', one_mul]
      using! mul_le_mul_of_nonneg_left (hi x) (inv_nonneg.mpr hn.le)
  · intro x
    simpa only [ContinuousLinearMap.smul_apply, ContinuousLinearEquiv.coe_coe, norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr hn.le), ← mul_assoc, mul_inv_cancel₀ hn.ne', one_mul,
      e.apply_symm_apply] using! he (e.symm x)

/-- A basis-free initial comparison, including the zero-dimensional case. -/
theorem exists_initial_Hilbert_comparison_finrank (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] :
    ∃ J : E →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)),
      (∀ x, ‖J x‖ ≤ ‖x‖) ∧ (∀ x, ‖x‖ ≤ (Module.finrank ℝ E : ℝ) * ‖J x‖) := by
  by_cases hz : Module.finrank ℝ E = 0
  · haveI : Subsingleton E := Module.finrank_zero_iff.mp hz
    exact ⟨0, fun x => by simp, fun x => by simp [Subsingleton.elim x 0]⟩
  · letI : Nonempty (Fin (Module.finrank ℝ E)) := ⟨⟨0, Nat.pos_of_ne_zero hz⟩⟩
    simpa only [Fintype.card_fin] using! exists_initial_Hilbert_comparison (Module.finBasis ℝ E)

end ConvexBodyChasing

end
end BundledModule118

/- Component source: ConvexBodyChasing.QSIteration -/
section BundledModule119
/-! # Iteration of the quantitative QS step

At each stage the new space carries its quotient norm. Exact composition keeps
only the last comparison constant. The numerical parameters control the sum
of all dimension losses, including integer rounding.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
universe u
namespace ConvexBodyChasing

attribute [local instance] Submodule.closed_of_finiteDimensional

theorem exists_iterated_QS (N r : ℕ) :
    ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
      {k : ℕ} (J : E →L[ℝ] EuclideanSpace ℝ (Fin k)),
      Module.finrank ℝ E ≤ N →
      (∀ x, ‖J x‖ ≤ ‖x‖) → (∀ x, ‖x‖ ≤ qsDistortionLevel r * ‖J x‖) →
      ∃ V : Submodule ℝ E, ∃ S : Submodule ℝ V,
        Module.finrank ℝ E ≤ Module.finrank ℝ (V ⧸ S) + qsDimensionLoss N r ∧
        ∃ k' : ℕ, ∃ J' : (V ⧸ S) →L[ℝ] EuclideanSpace ℝ (Fin k'),
          (∀ x, ‖J' x‖ ≤ ‖x‖) ∧ (∀ x, ‖x‖ ≤ qsDistortionLevel 0 * ‖J' x‖) := by
  induction r with
  | zero =>
      intro E _ _ _ k J _ hJ hE
      obtain ⟨V, S, hdim, J', hJ', hE'⟩ :=
        (NormedSubquotient.refl E).exists_quotient_comparison J hJ hE
      exact ⟨V, S, by simp only [hdim, qsDimensionLoss_zero, Nat.add_zero, le_refl],
        k, J', hJ', hE'⟩
  | succ r ih =>
      intro E _ _ _ k J hdim hJ hE
      by_cases hz : Module.finrank ℝ E = 0
      · haveI : Subsingleton E := Module.finrank_zero_iff.mp hz
        obtain ⟨V, S, _, J', hJ', hE'⟩ :=
          (NormedSubquotient.refl E).exists_quotient_comparison
            (0 : E →L[ℝ] EuclideanSpace ℝ (Fin 0))
            (fun x => by simp) (D := qsDistortionLevel 0) (fun x => by
              simp only [Subsingleton.elim x 0, norm_zero, map_zero, mul_zero, le_refl])
        exact ⟨V, S, by simp only [hz, Nat.zero_le], 0, J', hJ', hE'⟩
      · letI : Nonempty (Fin (Module.finrank ℝ E)) := ⟨⟨0, Nat.pos_of_ne_zero hz⟩⟩
        obtain ⟨V, S, hdim₁, J₁, hJ₁, hE₁⟩ := exists_quantitative_normed_QS
          (Module.finBasis ℝ E) J (qsDistortionLevel_ge_one (r + 1)) hJ hE
          (qsIterationCodimension_pos N r)
        have hcompare (x : V ⧸ S) : ‖x‖ ≤ qsDistortionLevel r * ‖J₁ x‖ := by
          exact (hE₁ x).trans (mul_le_mul_of_nonneg_right
            (by simpa only [Fintype.card_fin] using! quantitative_QS_radius_le_level hdim r)
            (norm_nonneg _))
        let q₁ := NormedSubquotient.ofQuotient V S
        obtain ⟨V₂, S₂, hdim₂, k₂, J₂, hJ₂, hE₂⟩ :=
          ih J₁ (q₁.finrank_le.trans hdim) hJ₁ hcompare
        let q₂ := NormedSubquotient.ofQuotient V₂ S₂
        obtain ⟨W, T, hdim₃, J', hJ', hE'⟩ :=
          (q₁.comp q₂).exists_quotient_comparison J₂ hJ₂ hE₂
        refine ⟨W, T, ?_, k₂, J', hJ', hE'⟩
        rw [hdim₃, qsDimensionLoss_succ]
        omega

/-- A quotient of a subspace of at least half the dimension, with an absolute
Euclidean comparison constant and no initial geometric assumptions. -/
theorem exists_uniform_QS_comparison (E : Type u) [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] :
    ∃ V : Submodule ℝ E, ∃ S : Submodule ℝ V,
      Module.finrank ℝ E ≤ 2 * Module.finrank ℝ (V ⧸ S) ∧
      ∃ k : ℕ, ∃ J : (V ⧸ S) →L[ℝ] EuclideanSpace ℝ (Fin k),
        (∀ x, ‖J x‖ ≤ ‖x‖) ∧ (∀ x, ‖x‖ ≤ qsDistortionLevel 0 * ‖J x‖) := by
  obtain ⟨J, hJ, hE⟩ := exists_initial_Hilbert_comparison_finrank E
  have hstart (x : E) :
      ‖x‖ ≤ qsDistortionLevel (Module.finrank ℝ E / 64) * ‖J x‖ :=
    (hE x).trans (mul_le_mul_of_nonneg_right
      (dimension_le_initial_qsDistortionLevel _) (norm_nonneg _))
  obtain ⟨V, S, hdim, k, J', hJ', hE'⟩ :=
    exists_iterated_QS (Module.finrank ℝ E) (Module.finrank ℝ E / 64) J le_rfl hJ hstart
  have hloss := twice_qsDimensionLoss_le (Module.finrank ℝ E)
  exact ⟨V, S, by omega, k, J', hJ', hE'⟩

end ConvexBodyChasing

end
end BundledModule119

/- Component source: ConvexBodyChasing.MilmanQS -/
section BundledModule120
/-! # Milman's quotient-of-a-subspace theorem

The quantitative QS estimate is iterated with exact normed quotients. The
resulting uniform Euclidean comparison is converted to the two unit-ball
inclusions used by the all-norms convex body chasing extension.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
universe u
namespace ConvexBodyChasing

attribute [local instance] Submodule.closed_of_finiteDimensional

theorem exists_ball_image_of_comparison {E H : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (J : E →L[ℝ] H) {M : ℝ} (hM : 0 < M)
    (hJ : ∀ x, ‖J x‖ ≤ ‖x‖) (hE : ∀ x, ‖x‖ ≤ M * ‖J x‖) :
    ∃ F : Submodule ℝ H, Module.finrank ℝ F = Module.finrank ℝ E ∧
      ∃ Q : E →L[ℝ] F,
        Metric.closedBall 0 1 ⊆ Q '' Metric.closedBall 0 1 ∧
        Q '' Metric.closedBall 0 1 ⊆ Metric.closedBall 0 M := by
  have hinj : Function.Injective J := by
    intro x y hxy
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    exact le_antisymm
      (by simpa only [map_sub, hxy, sub_self, norm_zero, mul_zero] using! hE (x - y)) (norm_nonneg _)
  let e : E ≃L[ℝ] J.range := (LinearEquiv.ofInjective J.toLinearMap hinj).toContinuousLinearEquiv
  let Q : E →L[ℝ] J.range := M • e.toContinuousLinearMap
  have he (x : E) : ‖e x‖ = ‖J x‖ := rfl
  refine ⟨J.range, e.toLinearEquiv.finrank_eq.symm, Q, ?_, ?_⟩
  · intro y hy
    have hn : ‖e.symm y‖ ≤ M * ‖y‖ := by
      simpa only [← he, e.apply_symm_apply] using! hE (e.symm y)
    have hlift : ‖M⁻¹ • e.symm y‖ ≤ ‖y‖ := by
      simpa only [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hM.le),
        ← mul_assoc, inv_mul_cancel₀ hM.ne', one_mul] using!
        mul_le_mul_of_nonneg_left hn (inv_nonneg.mpr hM.le)
    exact ⟨M⁻¹ • e.symm y,
      by simpa only [Metric.mem_closedBall, dist_zero_right] using!
        hlift.trans (show ‖y‖ ≤ 1 by simpa using! hy),
      by simp only [Q, ContinuousLinearMap.smul_apply, ContinuousLinearEquiv.coe_coe,
        map_smul, e.apply_symm_apply, smul_smul, inv_mul_cancel₀ hM.ne', one_smul]⟩
  · rintro y ⟨x, hx, rfl⟩
    have hn : ‖J x‖ ≤ 1 := (hJ x).trans (by simpa using! hx)
    simpa only [Q, ContinuousLinearMap.smul_apply, ContinuousLinearEquiv.coe_coe,
      Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg hM.le, he, mul_one]
      using! mul_le_mul_of_nonneg_left hn hM.le

/-- The geometric QS conclusion in the PDF, with a single explicit absolute
constant, for every finite-dimensional real normed space. -/
theorem exists_uniform_QS_ball_inclusions (E : Type u) [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] :
    ∃ V : Submodule ℝ E, ∃ k : ℕ, Module.finrank ℝ E ≤ 2 * k ∧
      ∃ Q : V →L[ℝ] EuclideanSpace ℝ (Fin k),
        Metric.closedBall 0 1 ⊆ Q '' Metric.closedBall 0 1 ∧
        Q '' Metric.closedBall 0 1 ⊆ Metric.closedBall 0 (qsDistortionLevel 0) := by
  obtain ⟨V, S, hdim, _, J, hJ, hE⟩ := exists_uniform_QS_comparison E
  obtain ⟨F, hFdim, Q, hcover, hbound⟩ := exists_ball_image_of_comparison J
    (lt_of_lt_of_le zero_lt_one (qsDistortionLevel_ge_one 0)) hJ hE
  let T := Q.comp (normedQuotientMap S)
  have hT : T '' Metric.closedBall 0 1 = Q '' Metric.closedBall 0 1 :=
    image_closedBall_comp _ _ 1 (normedQuotientMap_image_closedBall S 1)
  let e := (stdOrthonormalBasis ℝ F).repr
  refine ⟨V, Module.finrank ℝ F, by simpa only [hFdim] using! hdim,
    e.toLinearIsometry.toContinuousLinearMap.comp T, ?_, ?_⟩
  · rw [ContinuousLinearMap.coe_comp', Set.image_comp, hT]
    simpa only [e.image_closedBall, map_zero] using! Set.image_mono (f := e) hcover
  · rw [ContinuousLinearMap.coe_comp', Set.image_comp, hT]
    simpa only [e.image_closedBall, map_zero] using! Set.image_mono (f := e) hbound

/-- Milman's QS theorem with the quantifier for the absolute constant outside
the quantifiers for the space and its norm. -/
theorem milman_QS :
    ∃ M : ℝ, 1 ≤ M ∧
      ∀ (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E],
        ∃ V : Submodule ℝ E, ∃ k : ℕ, Module.finrank ℝ E ≤ 2 * k ∧
          ∃ Q : V →L[ℝ] EuclideanSpace ℝ (Fin k),
            Metric.closedBall 0 1 ⊆ Q '' Metric.closedBall 0 1 ∧
            Q '' Metric.closedBall 0 1 ⊆ Metric.closedBall 0 M :=
  ⟨qsDistortionLevel 0, qsDistortionLevel_ge_one 0, exists_uniform_QS_ball_inclusions⟩

end ConvexBodyChasing

end
end BundledModule120

end CBCProve2MeProofs.Milman

theorem solution : ∃ M : ℝ, 1 ≤ M ∧
    ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X],
      ∃ (E : Submodule ℝ X) (k : ℕ) (Q : E →ₗ[ℝ] EuclideanSpace ℝ (Fin k)),
        (Module.finrank ℝ X : ℝ) / 2 ≤ k ∧
        Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) 1 ⊆ Q '' {x : E | ‖x‖ ≤ 1} ∧
        Q '' {x : E | ‖x‖ ≤ 1} ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) M := by
  obtain ⟨M, hM, hqs⟩ := CBCProve2MeProofs.Milman.ConvexBodyChasing.milman_QS.{0}
  refine ⟨M, hM, ?_⟩
  intro X _ _ _
  obtain ⟨E, k, hk, Q, hcover, hbound⟩ := hqs X
  refine ⟨E, k, Q.toLinearMap, ?_, ?_, ?_⟩
  · exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2
      (by exact_mod_cast hk.trans_eq (Nat.mul_comm 2 k))
  · simpa only [Metric.closedBall, dist_zero_right] using! hcover
  · simpa only [Metric.closedBall, dist_zero_right] using! hbound
