-- Prove2me | solution 1 for FunctionalInequalities.Energy.SmoothGradient.relaxation_le_asymptoticLipschitz_of_lipschitzWith_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:57:25.696584+00:00
-- url     : https://prove2.me/submissions/f0a0bf49-9edc-404b-ad80-571827777172

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
import Theorems.Thm_FunctionalInequalities_Energy_limsup_enorm_gradient_mollify_le_408915f

section
noncomputable section
open Filter Topology
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Energy
end FunctionalInequalities.Energy
open FunctionalInequalities FunctionalInequalities.Energy
universe u v
section
namespace FunctionalInequalities.Energy.PreEnergy
end FunctionalInequalities.Energy.PreEnergy
open FunctionalInequalities FunctionalInequalities.Energy FunctionalInequalities.Energy.PreEnergy
variable {X : Type u} [TopologicalSpace X] (P : PreEnergy X)
/-- Every particular approximating sequence gives an upper bound for the relaxed energy. -/
theorem FunctionalInequalities.Energy.PreEnergy.sequentialRelaxation_le_sequenceEnergy {x : X} (f : P.ApproximatingSequence x) :
    P.sequentialRelaxation x ≤ P.sequenceEnergy f :=
  iInf_le _ f
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
namespace FunctionalInequalities.Energy.SmoothGradient
end FunctionalInequalities.Energy.SmoothGradient
open FunctionalInequalities FunctionalInequalities.Energy FunctionalInequalities.Energy.SmoothGradient
section Recovery
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
namespace FunctionalInequalities.Energy.SmoothGradient
end FunctionalInequalities.Energy.SmoothGradient
open FunctionalInequalities.Energy.SmoothGradient in
/-- smooth recovery.  The smooth-gradient relaxation of a globally Lipschitz test is at most its
asymptotic-Lipschitz energy.  The recovery sequence is the mollification at radius `2 / (j + 1)`;
the global Lipschitz constant dominates the integrands uniformly, so reverse Fatou converts the
pointwise bound `limsup ‖∇(g ⋆ ρ_R)(x)‖ ≤ Lip_a g (x)` into the energy bound. -/
theorem solution (ν : ProbabilityMeasure V)
    {g : V → ℝ} {K : ℝ≥0} (hlip : LipschitzWith K g) (hmem : MemLp g 2 (ν : Measure V)) :
    FunctionalInequalities.Energy.SmoothGradient.relaxation ν (hmem.toLp g) ≤ FunctionalInequalities.Energy.AsymptoticLipschitz.energy ν g := by
  classical
  set m : Measure V := Measure.addHaar with hm
  set gj : ℕ → V → ℝ := fun j ↦ FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.mollify m (FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.radius j) g with hgj
  have hRj : ∀ j, (0 : ℝ) < FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.radius j := FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.radius_pos
  have hlipj : ∀ j, LipschitzWith K (gj j) := fun j ↦ FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.lipschitzWith_mollify m (hRj j) hlip
  have hsmooth : ∀ j, ContDiff ℝ ∞ (gj j) := fun j ↦ FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.contDiff_mollify m (hRj j) hlip.continuous
  have hbd : ∀ j, ∀ x, ‖gj j x - g x‖ ≤ (K : ℝ) * (2 * FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.radius j) := fun j x ↦
    FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.norm_mollify_sub_le m (hRj j) hlip x
  have hradle : ∀ j, FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.radius j ≤ 1 := by
    intro j
    rw [FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.radius, div_le_one (by positivity)]
    have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith
  have hML : ∀ j, MemLp (gj j) 2 (ν : Measure V) := by
    intro j
    have hdiff : MemLp (fun x ↦ gj j x - g x) 2 (ν : Measure V) := by
      refine MemLp.of_bound ?_ ((K : ℝ) * (2 * FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.radius j)) (ae_of_all _ fun x ↦ hbd j x)
      exact ((hlipj j).continuous.sub hlip.continuous).aestronglyMeasurable
    have hrw : gj j = fun x ↦ (gj j x - g x) + g x := by funext x; ring
    rw [hrw]
    exact hdiff.add hmem
  have hgradint : ∀ j, Integrable (fun x ↦ ‖gradient (gj j) x‖ ^ 2) (ν : Measure V) := by
    intro j
    refine Integrable.mono' (integrable_const ((K : ℝ) ^ 2))
      ((FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.measurable_gradient (gj j)).norm.pow_const 2).aestronglyMeasurable
      (ae_of_all _ fun x ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [norm_nonneg (gradient (gj j) x), FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.norm_gradient_le_of_lipschitz (hlipj j) x]
  set T : ℕ → FunctionalInequalities.Energy.SmoothGradient.Test ν := fun j ↦
    { toFun := gj j
      contDiff := hsmooth j
      memLp_two := hML j
      gradient_sq_integrable := hgradint j } with hT
  have hconv : Tendsto (fun j ↦ (T j).toL2) atTop (𝓝 (hmem.toLp g)) := by
    refine (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun j ↦ gj j) hML g hmem).mpr ?_
    refine FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.tendsto_eLpNorm_zero_of_dominated (ν : Measure V) (p := 2) (by norm_num) (by norm_num)
      (F := fun j ↦ gj j - g) (bound := fun _ ↦ (K : ℝ) * 2) (fun j ↦ ?_) (memLp_const _)
      (fun j ↦ ae_of_all _ fun x ↦ ?_) (ae_of_all _ fun x ↦ ?_)
    · exact ((hlipj j).continuous.sub hlip.continuous).aestronglyMeasurable
    · refine (hbd j x).trans ?_
      have := hradle j
      nlinarith [K.coe_nonneg, (hRj j).le]
    · refine squeeze_zero_norm (fun j ↦ hbd j x) ?_
      have : Tendsto (fun j ↦ (K : ℝ) * (2 * FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.radius j)) atTop (𝓝 ((K : ℝ) * (2 * 0))) :=
        (FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.tendsto_radius.const_mul (2 : ℝ)).const_mul (K : ℝ)
      simpa using this
  have henergy_eq : ∀ j, (((FunctionalInequalities.Energy.SmoothGradient.preEnergy ν).energy (T j) : ℝ≥0) : ℝ≥0∞) =
      ∫⁻ x, ‖gradient (gj j) x‖ₑ ^ 2 ∂(ν : Measure V) := by
    intro j
    have h1 : ∫⁻ x, ‖gradient (gj j) x‖ₑ ^ 2 ∂(ν : Measure V)
        = ∫⁻ x, ENNReal.ofReal (‖gradient (gj j) x‖ ^ 2) ∂(ν : Measure V) := by
      refine lintegral_congr fun x ↦ ?_
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    rw [h1, ← ofReal_integral_eq_lintegral_ofReal (hgradint j) (ae_of_all _ fun x ↦ sq_nonneg _)]
    show _ = ENNReal.ofReal ((T j).energy : ℝ)
    rw [ENNReal.ofReal_coe_nnreal]
    rfl
  refine le_trans ((FunctionalInequalities.Energy.SmoothGradient.preEnergy ν).sequentialRelaxation_le_sequenceEnergy
    (⟨T, hconv⟩ : (FunctionalInequalities.Energy.SmoothGradient.preEnergy ν).ApproximatingSequence (hmem.toLp g))) ?_
  have hliminf : (FunctionalInequalities.Energy.SmoothGradient.preEnergy ν).sequenceEnergy
      (⟨T, hconv⟩ : (FunctionalInequalities.Energy.SmoothGradient.preEnergy ν).ApproximatingSequence (hmem.toLp g)) =
      liminf (fun j ↦ ∫⁻ x, ‖gradient (gj j) x‖ₑ ^ 2 ∂(ν : Measure V)) atTop := by
    show liminf (fun j ↦ (((FunctionalInequalities.Energy.SmoothGradient.preEnergy ν).energy (T j) : ℝ≥0) : ℝ≥0∞)) atTop = _
    simp_rw [henergy_eq]
  rw [hliminf]
  have hmeas : ∀ j, Measurable (fun x ↦ ‖gradient (gj j) x‖ₑ ^ 2) := fun j ↦
    ((FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.measurable_gradient (gj j)).enorm).pow_const 2
  have hbound : ∀ j, (fun x ↦ ‖gradient (gj j) x‖ₑ ^ 2) ≤ᵐ[(ν : Measure V)]
      fun _ ↦ ((K : ℝ≥0∞)) ^ 2 := by
    intro j
    refine ae_of_all _ fun x ↦ ?_
    refine pow_le_pow_left' ?_ 2
    rw [← ofReal_norm, ← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal (FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.norm_gradient_le_of_lipschitz (hlipj j) x)
  have hfin : ∫⁻ _, ((K : ℝ≥0∞)) ^ 2 ∂(ν : Measure V) ≠ ⊤ := by
    rw [lintegral_const, measure_univ, mul_one]
    exact ENNReal.pow_ne_top ENNReal.coe_ne_top
  calc liminf (fun j ↦ ∫⁻ x, ‖gradient (gj j) x‖ₑ ^ 2 ∂(ν : Measure V)) atTop
      ≤ limsup (fun j ↦ ∫⁻ x, ‖gradient (gj j) x‖ₑ ^ 2 ∂(ν : Measure V)) atTop :=
        liminf_le_limsup (by isBoundedDefault) (by isBoundedDefault)
    _ ≤ ∫⁻ x, limsup (fun j ↦ ‖gradient (gj j) x‖ₑ ^ 2) atTop ∂(ν : Measure V) :=
        MeasureTheory.limsup_lintegral_le _ hmeas hbound hfin
    _ ≤ FunctionalInequalities.Energy.AsymptoticLipschitz.energy ν g := by
        refine lintegral_mono fun x ↦ ?_
        have hmono : Monotone (fun a : ℝ≥0∞ ↦ a ^ 2) := fun a b hab ↦ pow_le_pow_left' hab 2
        have hmap : (limsup (fun j ↦ ‖gradient (gj j) x‖ₑ) atTop) ^ 2
            = limsup ((fun a : ℝ≥0∞ ↦ a ^ 2) ∘ fun j ↦ ‖gradient (gj j) x‖ₑ) atTop :=
          hmono.map_limsup_of_continuousAt (F := atTop) _
            ((ENNReal.continuous_pow 2).continuousAt)
        rw [show (fun j ↦ ‖gradient (gj j) x‖ₑ ^ 2) =
          (fun a : ℝ≥0∞ ↦ a ^ 2) ∘ (fun j ↦ ‖gradient (gj j) x‖ₑ) from rfl, ← hmap]
        exact pow_le_pow_left' (FunctionalInequalities.Energy.limsup_enorm_gradient_mollify_le_408915f m hlip.continuous x) 2
