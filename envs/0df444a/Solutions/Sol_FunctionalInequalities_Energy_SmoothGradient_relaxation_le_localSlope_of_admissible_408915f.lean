-- Prove2me | solution 1 for FunctionalInequalities.Energy.SmoothGradient.relaxation_le_localSlope_of_admissible_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:59:43.775736+00:00
-- url     : https://prove2.me/submissions/078bff7c-df55-4a2b-be44-9f383c4968c6

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Approximation
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Kernel
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Measurable
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_Slope_Recovery
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_Functional
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_LocalSlope_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_LocalSlope_Relaxation
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Relaxation_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Intrinsic_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_L2_MeanVariance
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_AffineSupport
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Inv
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Probability.Moments.Variance
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Theorems.Thm_FunctionalInequalities_Energy_LocalSlope_apply_mul_le_408915f
import Theorems.Thm_FunctionalInequalities_Energy_LocalSlope_lowerSemicontinuous_secant_408915f
import Theorems.Thm_FunctionalInequalities_Energy_PreEnergy_lowerSemicontinuous_sequentialRelaxation_408915f
import Theorems.Thm_FunctionalInequalities_Energy_SmoothGradient_relaxation_le_localSlope_of_lipschitzWith_408915f
import Theorems.Thm_FunctionalInequalities_Energy_exists_lipschitzWith_of_eq_zero_outside_ball_408915f
import Theorems.Thm_FunctionalInequalities_Energy_locallyLipschitz_mul_408915f
import Theorems.Thm_FunctionalInequalities_Energy_sq_add_le_mul_sq_add_408915f

section
noncomputable section
open MeasureTheory Filter Topology Set
open FunctionalInequalities.Energy.Euclidean.LipschitzApproximation
open scoped ENNReal NNReal ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Energy
end FunctionalInequalities.Energy
open FunctionalInequalities FunctionalInequalities.Energy
universe u
section
namespace FunctionalInequalities.Energy.LocalSlope
end FunctionalInequalities.Energy.LocalSlope
open FunctionalInequalities FunctionalInequalities.Energy FunctionalInequalities.Energy.LocalSlope
section Metric
variable {X : Type*} [MetricSpace X]
theorem FunctionalInequalities.Energy.LocalSlope.apply_eq_iInf_secant (f : X → ℝ) (x : X) :
    apply f x = ⨅ (r : ℝ) (_ : 0 < r), secant f r x :=
  rfl
/-- Every positive radius bounds the local slope from above. -/
theorem FunctionalInequalities.Energy.LocalSlope.apply_le_secant (f : X → ℝ) {r : ℝ} (hr : 0 < r) (x : X) :
    apply f x ≤ secant f r x :=
  iInf_le_of_le r (iInf_le _ hr)
/-- The secant supremum is monotone in the radius. -/
theorem FunctionalInequalities.Energy.LocalSlope.secant_mono (f : X → ℝ) {r r' : ℝ} (h : r ≤ r') (x : X) :
    secant f r x ≤ secant f r' x := by
  refine iSup_le fun y ↦ iSup_le fun hy ↦ ?_
  exact le_iSup₂_of_le y (hy.trans_le h) le_rfl
end Metric
end
end
end
end
end

noncomputable section
open MeasureTheory Filter Topology Set
open FunctionalInequalities.Energy.Euclidean.LipschitzApproximation
open scoped ENNReal NNReal ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Energy
end FunctionalInequalities.Energy
open FunctionalInequalities FunctionalInequalities.Energy
universe u
section
namespace FunctionalInequalities.Energy.LocalSlope
end FunctionalInequalities.Energy.LocalSlope
open FunctionalInequalities FunctionalInequalities.Energy FunctionalInequalities.Energy.LocalSlope
section Measurability
variable {X : Type*} [MetricSpace X]
/-- The local slope is the countable infimum of the secant suprema at the radii `1 / (m + 1)`. -/
theorem FunctionalInequalities.Energy.LocalSlope.apply_eq_iInf_nat (f : X → ℝ) (x : X) :
    apply f x = ⨅ m : ℕ, secant f (1 / ((m : ℝ) + 1)) x := by
  refine le_antisymm (le_iInf fun m ↦ apply_le_secant f (by positivity) x) ?_
  rw [apply_eq_iInf_secant]
  refine le_iInf fun r ↦ le_iInf fun hr ↦ ?_
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hr
  exact le_trans (iInf_le _ m) (secant_mono f hm.le x)
variable [MeasurableSpace X] [OpensMeasurableSpace X]
/-- `C1`.  The local slope of a continuous function is Borel measurable. -/
theorem FunctionalInequalities.Energy.LocalSlope.measurable_apply {f : X → ℝ} (hf : Continuous f) : Measurable (apply f) := by
  have h : apply f = fun x ↦ ⨅ m : ℕ, secant f (1 / ((m : ℝ) + 1)) x :=
    funext fun x ↦ apply_eq_iInf_nat f x
  rw [h]
  exact Measurable.iInf fun m ↦ (lowerSemicontinuous_secant_408915f hf _).measurable
end Measurability
end
section Density
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
/-- A lower-semicontinuous functional does not exceed the limit inferior along a convergent
sequence. -/
theorem FunctionalInequalities.Energy.le_liminf_of_lowerSemicontinuous {X : Type*} [TopologicalSpace X] (Q : X → ℝ≥0∞)
    (hQ : LowerSemicontinuous Q) {x : X} {a : ℕ → X} (h : Tendsto a atTop (𝓝 x)) :
    Q x ≤ liminf (fun n ↦ Q (a n)) atTop := by
  refine le_of_forall_lt fun cc hcc ↦ ?_
  obtain ⟨d, hcd, hd⟩ := exists_between hcc
  have heventually := h.eventually (hQ x d hd)
  exact hcd.trans_le (le_liminf_of_le (by isBoundedDefault)
    (heventually.mono fun _ hn ↦ hn.le))
end Density
section General
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
section
namespace FunctionalInequalities.Energy.SmoothGradient
end FunctionalInequalities.Energy.SmoothGradient
open FunctionalInequalities FunctionalInequalities.Energy FunctionalInequalities.Energy.SmoothGradient
namespace FunctionalInequalities.Energy.SmoothGradient
end FunctionalInequalities.Energy.SmoothGradient
open FunctionalInequalities.Energy.SmoothGradient in
/-- `C5`.  Density for every admissible local-slope test: cutting off by the smooth bump
`scaled (n + 1)` produces globally Lipschitz tests converging in `L²(ν)` whose energies converge,
after Young's inequality, to the local-slope energy of the test. -/
theorem solution (ν : ProbabilityMeasure V) {g : V → ℝ}
    (hg : FunctionalInequalities.Energy.LocalSlope.Admissible ν g) :
    FunctionalInequalities.Energy.SmoothGradient.relaxation ν (hg.memLp_two.toLp g) ≤ FunctionalInequalities.Energy.LocalSlope.energy ν g := by
  classical
  set E : ℝ≥0∞ := FunctionalInequalities.Energy.LocalSlope.energy ν g with hE
  have hEtop : E ≠ ⊤ := hg.finite_energy
  have hgcont : Continuous g := hg.locallyLipschitz.continuous
  have hmeas_s : Measurable (FunctionalInequalities.Energy.LocalSlope.apply g) := FunctionalInequalities.Energy.LocalSlope.measurable_apply hgcont
  -- the `L²` mass of the test
  set G : ℝ≥0∞ := ∫⁻ x, ‖g x‖ₑ ^ 2 ∂(ν : Measure V) with hG
  have hGtop : G ≠ ⊤ := by
    have hint : Integrable (fun x ↦ ‖g x‖ ^ 2) (ν : Measure V) :=
      (memLp_two_iff_integrable_sq_norm hg.memLp_two.1).mp hg.memLp_two
    have heq : G = ENNReal.ofReal (∫ x, ‖g x‖ ^ 2 ∂(ν : Measure V)) := by
      rw [hG, ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun x ↦ sq_nonneg _)]
      exact lintegral_congr fun x ↦ by
        rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    rw [heq]
    exact ENNReal.ofReal_ne_top
  obtain ⟨Mb, hMb0, hMb⟩ := FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.exists_bound_fderiv_bump (E := V)
  set N : ℕ → ℝ≥0 := fun n ↦ ((((n : ℝ) + 1)⁻¹ * Mb).toNNReal) with hNdef
  have hNtend : Tendsto (fun n : ℕ ↦ ((N n : ℝ≥0) : ℝ≥0∞)) atTop (𝓝 0) := by
    rw [show (0 : ℝ≥0∞) = ((0 : ℝ≥0) : ℝ≥0∞) from rfl]
    refine ENNReal.tendsto_coe.2 ?_
    rw [← NNReal.tendsto_coe]
    have heq : (fun n : ℕ ↦ ((N n : ℝ≥0) : ℝ)) = fun n : ℕ ↦ (((n : ℝ) + 1)⁻¹ * Mb) := by
      funext n
      rw [hNdef]
      exact Real.coe_toNNReal _ (by positivity)
    rw [heq]
    have : Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1)⁻¹ * Mb) atTop (𝓝 (0 * Mb)) := by
      refine Tendsto.mul_const Mb ?_
      simpa [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa using this
  -- the cutoffs
  set q : ℕ → V → ℝ := fun n x ↦ g x * FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled ((n : ℝ) + 1) x with hqdef
  have hRpos : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n ↦ by positivity
  have hscaled1 : ∀ (n : ℕ) (x : V), |FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled ((n : ℝ) + 1) x| ≤ 1 := by
    intro n x
    rw [abs_of_nonneg (FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled_nonneg _ x)]
    exact FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled_le_one _ x
  have hscaledlip : ∀ n : ℕ, LipschitzWith (N n) (FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled (E := V) ((n : ℝ) + 1)) := fun n ↦
    FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.lipschitzWith_scaled (hRpos n) hMb0 hMb
  have hqloc : ∀ n, LocallyLipschitz (q n) := fun n ↦
    FunctionalInequalities.Energy.locallyLipschitz_mul_408915f hg.locallyLipschitz (hscaledlip n) (hscaled1 n)
  have hqzero : ∀ (n : ℕ) (x : V), 2 * ((n : ℝ) + 1) ≤ ‖x‖ → q n x = 0 := by
    intro n x hx
    rw [hqdef]
    simp only
    rw [FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled_eq_zero (hRpos n) hx, mul_zero]
  have hKqex : ∀ n : ℕ, ∃ K : ℝ≥0, LipschitzWith K (q n) := fun n ↦
    FunctionalInequalities.Energy.exists_lipschitzWith_of_eq_zero_outside_ball_408915f (hqloc n) (hqzero n)
  choose Kq hKq using hKqex
  have hqabs : ∀ (n : ℕ) (x : V), |q n x| ≤ |g x| := by
    intro n x
    rw [hqdef]
    simp only
    rw [abs_mul]
    calc |g x| * |FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled ((n : ℝ) + 1) x| ≤ |g x| * 1 :=
          mul_le_mul_of_nonneg_left (hscaled1 n x) (abs_nonneg _)
      _ = |g x| := mul_one _
  have hqmem : ∀ n, MemLp (q n) 2 (ν : Measure V) := by
    intro n
    refine hg.memLp_two.mono ((hqloc n).continuous.aestronglyMeasurable) (ae_of_all _ fun x ↦ ?_)
    simpa [Real.norm_eq_abs] using hqabs n x
  have hqconv : Tendsto (fun n ↦ (hqmem n).toLp (q n)) atTop (𝓝 (hg.memLp_two.toLp g)) := by
    refine (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun n ↦ q n) hqmem g hg.memLp_two).mpr ?_
    refine FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.tendsto_eLpNorm_zero_of_dominated (ν : Measure V) (p := 2) (by norm_num) (by norm_num)
      (F := fun n ↦ q n - g) (bound := fun x ↦ ‖g x‖) (fun n ↦ ?_) hg.memLp_two.norm
      (fun n ↦ ae_of_all _ fun x ↦ ?_) (ae_of_all _ fun x ↦ ?_)
    · exact ((hqloc n).continuous.sub hgcont).aestronglyMeasurable
    · simp only [Pi.sub_apply]
      have h2 : q n x - g x = g x * (FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled ((n : ℝ) + 1) x - 1) := by
        rw [hqdef]; simp only; ring
      rw [h2, Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
      have h3 : |FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled ((n : ℝ) + 1) x - 1| ≤ 1 := by
        rw [abs_le]
        constructor
        · have := FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled_le_one ((n : ℝ) + 1) x
          have := FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled_nonneg ((n : ℝ) + 1) x
          linarith
        · have := FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled_nonneg ((n : ℝ) + 1) x
          have := FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled_le_one ((n : ℝ) + 1) x
          linarith
      calc |g x| * |FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled ((n : ℝ) + 1) x - 1| ≤ |g x| * 1 :=
            mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
        _ = |g x| := mul_one _
    · have hev : ∀ᶠ n : ℕ in atTop, (q n - g) x = 0 := by
        obtain ⟨n₀, hn₀⟩ := exists_nat_ge ‖x‖
        filter_upwards [eventually_ge_atTop n₀] with n hn
        have hle : ‖x‖ ≤ (n : ℝ) + 1 := by
          have : (n₀ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
          linarith
        simp [hqdef, FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled_eq_one (hRpos n) hle]
      exact Tendsto.congr' (by filter_upwards [hev] with n hn; rw [hn]) tendsto_const_nhds
  -- the parametrized energy bound
  have key : ∀ θ : ℝ≥0, 0 < θ →
      FunctionalInequalities.Energy.SmoothGradient.relaxation ν (hg.memLp_two.toLp g) ≤ (1 + (θ : ℝ≥0∞)) * E := by
    intro θ hθ
    have hθtop : (1 + (θ : ℝ≥0∞)⁻¹) ≠ ⊤ :=
      ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, by
        rw [← ENNReal.coe_inv hθ.ne']
        exact ENNReal.coe_ne_top⟩
    have hbound : ∀ n, FunctionalInequalities.Energy.SmoothGradient.relaxation ν ((hqmem n).toLp (q n)) ≤
        (1 + (θ : ℝ≥0∞)) * E + (1 + (θ : ℝ≥0∞)⁻¹) * (((N n : ℝ≥0) : ℝ≥0∞) ^ 2 * G) := by
      intro n
      refine le_trans (FunctionalInequalities.Energy.SmoothGradient.relaxation_le_localSlope_of_lipschitzWith_408915f ν (hKq n) (hqmem n)) ?_
      have hpt : ∀ x, FunctionalInequalities.Energy.LocalSlope.apply (q n) x ^ 2 ≤
          (1 + (θ : ℝ≥0∞)) * FunctionalInequalities.Energy.LocalSlope.apply g x ^ 2 +
            (1 + (θ : ℝ≥0∞)⁻¹) * (‖g x‖ₑ ^ 2 * ((N n : ℝ≥0) : ℝ≥0∞) ^ 2) := by
        intro x
        have h1 : FunctionalInequalities.Energy.LocalSlope.apply (q n) x ≤
            FunctionalInequalities.Energy.LocalSlope.apply g x + ENNReal.ofReal |g x| * ((N n : ℝ≥0) : ℝ≥0∞) :=
          FunctionalInequalities.Energy.LocalSlope.apply_mul_le_408915f g _ (hscaledlip n) (hscaled1 n) x
        refine (pow_le_pow_left' h1 2).trans ?_
        refine (FunctionalInequalities.Energy.sq_add_le_mul_sq_add_408915f hθ _ _).trans ?_
        refine add_le_add le_rfl (le_of_eq ?_)
        have hgx : ENNReal.ofReal |g x| = ‖g x‖ₑ := by
          rw [← Real.norm_eq_abs, ofReal_norm]
        rw [hgx, mul_pow]
      calc FunctionalInequalities.Energy.LocalSlope.energy ν (q n) ≤ ∫⁻ x, ((1 + (θ : ℝ≥0∞)) * FunctionalInequalities.Energy.LocalSlope.apply g x ^ 2 +
              (1 + (θ : ℝ≥0∞)⁻¹) * (‖g x‖ₑ ^ 2 * ((N n : ℝ≥0) : ℝ≥0∞) ^ 2)) ∂(ν : Measure V) :=
            lintegral_mono hpt
        _ = (1 + (θ : ℝ≥0∞)) * E + (1 + (θ : ℝ≥0∞)⁻¹) * (((N n : ℝ≥0) : ℝ≥0∞) ^ 2 * G) := by
            rw [lintegral_add_left ((hmeas_s.pow_const 2).const_mul _),
              lintegral_const_mul _ (hmeas_s.pow_const 2),
              lintegral_const_mul _ (((hgcont.measurable.enorm).pow_const 2).mul_const _)]
            rw [lintegral_mul_const _ (hgcont.measurable.enorm.pow_const 2)]
            rw [hG, hE]
            simp only [FunctionalInequalities.Energy.LocalSlope.energy]
            ring
    have herr : Tendsto (fun n ↦ (1 + (θ : ℝ≥0∞)) * E +
        (1 + (θ : ℝ≥0∞)⁻¹) * (((N n : ℝ≥0) : ℝ≥0∞) ^ 2 * G)) atTop
        (𝓝 ((1 + (θ : ℝ≥0∞)) * E)) := by
      have h1 : Tendsto (fun n ↦ ((N n : ℝ≥0) : ℝ≥0∞) ^ 2) atTop (𝓝 0) := by
        have := (ENNReal.continuous_pow 2).tendsto (0 : ℝ≥0∞) |>.comp hNtend
        simpa [Function.comp_def] using this
      have h2 : Tendsto (fun n ↦ ((N n : ℝ≥0) : ℝ≥0∞) ^ 2 * G) atTop (𝓝 0) := by
        have := ENNReal.Tendsto.mul_const h1 (Or.inr hGtop)
        simpa using this
      have h3 : Tendsto (fun n ↦ (1 + (θ : ℝ≥0∞)⁻¹) * (((N n : ℝ≥0) : ℝ≥0∞) ^ 2 * G)) atTop
          (𝓝 0) := by
        have := ENNReal.Tendsto.const_mul h2 (Or.inr hθtop)
        simpa using this
      simpa using tendsto_const_nhds.add h3
    have hlsc := FunctionalInequalities.Energy.le_liminf_of_lowerSemicontinuous (fun f ↦ FunctionalInequalities.Energy.SmoothGradient.relaxation ν f)
      (FunctionalInequalities.Energy.SmoothGradient.preEnergy ν).lowerSemicontinuous_sequentialRelaxation_408915f hqconv
    refine hlsc.trans ?_
    refine le_trans (liminf_le_liminf (Eventually.of_forall hbound)) ?_
    exact le_of_eq herr.liminf_eq
  -- let the parameter tend to zero
  set θ : ℕ → ℝ≥0 := fun k ↦ ((k : ℝ≥0) + 1)⁻¹ with hθdef
  have hθ0 : ∀ k, 0 < θ k := fun k ↦ by
    rw [hθdef]
    exact inv_pos.2 (by positivity)
  have hθtend : Tendsto (fun k : ℕ ↦ ((θ k : ℝ≥0) : ℝ≥0∞)) atTop (𝓝 0) := by
    rw [show (0 : ℝ≥0∞) = ((0 : ℝ≥0) : ℝ≥0∞) from rfl]
    refine ENNReal.tendsto_coe.2 ?_
    rw [← NNReal.tendsto_coe]
    have heq : (fun k : ℕ ↦ ((θ k : ℝ≥0) : ℝ)) = fun k : ℕ ↦ ((k : ℝ) + 1)⁻¹ := by
      funext k
      rw [hθdef]
      push_cast
      ring
    rw [heq]
    simpa [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hlim : Tendsto (fun k ↦ (1 + ((θ k : ℝ≥0) : ℝ≥0∞)) * E) atTop (𝓝 E) := by
    have h1 : Tendsto (fun k ↦ (1 + ((θ k : ℝ≥0) : ℝ≥0∞))) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.add hθtend
    have := ENNReal.Tendsto.mul_const h1 (Or.inr hEtop)
    simpa using this
  exact ge_of_tendsto hlim (Eventually.of_forall fun k ↦ key (θ k) (hθ0 k))
