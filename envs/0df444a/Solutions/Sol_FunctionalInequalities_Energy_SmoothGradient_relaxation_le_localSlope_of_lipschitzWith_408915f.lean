-- Prove2me | solution 1 for FunctionalInequalities.Energy.SmoothGradient.relaxation_le_localSlope_of_lipschitzWith_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:58:26.8434+00:00
-- url     : https://prove2.me/submissions/e9a82d61-966c-447c-856f-42d74b0571e7

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
import Theorems.Thm_FunctionalInequalities_Energy_LocalSlope_exists_patch_408915f
import Theorems.Thm_FunctionalInequalities_Energy_LocalSlope_lowerSemicontinuous_secant_408915f
import Theorems.Thm_FunctionalInequalities_Energy_PreEnergy_lowerSemicontinuous_sequentialRelaxation_408915f
import Theorems.Thm_FunctionalInequalities_Energy_SmoothGradient_relaxation_le_asymptoticLipschitz_of_lipschitzWith_408915f

section
noncomputable section
open MeasureTheory Filter Topology
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
namespace FunctionalInequalities.Energy.AsymptoticLipschitz
end FunctionalInequalities.Energy.AsymptoticLipschitz
open FunctionalInequalities FunctionalInequalities.Energy FunctionalInequalities.Energy.AsymptoticLipschitz
section Metric
variable {X : Type*} [MetricSpace X]
/-- A globally Lipschitz function has asymptotic Lipschitz constant at most its constant. -/
theorem FunctionalInequalities.Energy.AsymptoticLipschitz.apply_le_of_lipschitzWith {K : ℝ≥0} {f : X → ℝ} (hf : LipschitzWith K f) (x : X) :
    apply f x ≤ K := by
  unfold apply
  refine iInf_le_of_le 1 (iInf_le_of_le zero_lt_one ?_)
  refine iSup_le fun y ↦ iSup_le fun _ ↦ iSup_le fun z ↦ iSup_le fun _ ↦ ?_
  rw [← ENNReal.ofReal_coe_nnreal]
  apply ENNReal.ofReal_le_ofReal
  rcases eq_or_ne (dist y z) 0 with h0 | h0
  · rw [h0, div_zero]
    exact K.coe_nonneg
  · exact (div_le_iff₀ (dist_nonneg.lt_of_ne (Ne.symm h0))).2 (hf.dist_le_mul y z)
end Metric
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
end
end
end
end
end

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
/-- In `ℝ≥0∞` every value is dominated by `1` plus its square. -/
theorem FunctionalInequalities.Energy.le_one_add_sq (s : ℝ≥0∞) : s ≤ 1 + s ^ 2 := by
  rcases le_total s 1 with h | h
  · exact h.trans le_self_add
  · calc s = s * 1 := (mul_one s).symm
      _ ≤ s * s := mul_le_mul_right h s
      _ = s ^ 2 := (sq s).symm
      _ ≤ 1 + s ^ 2 := le_add_self
/-- The band expansion used by the density estimate. -/
theorem FunctionalInequalities.Energy.sq_add_two_mul_le (s a : ℝ≥0∞) :
    (s + 2 * a) ^ 2 ≤ (1 + 4 * a) * s ^ 2 + (4 * a + 4 * a ^ 2) := by
  have h1 : (s + 2 * a) ^ 2 = s ^ 2 + 4 * a * s + 4 * a ^ 2 := by ring
  rw [h1]
  calc s ^ 2 + 4 * a * s + 4 * a ^ 2 ≤ s ^ 2 + 4 * a * (1 + s ^ 2) + 4 * a ^ 2 := by
        gcongr
        exact le_one_add_sq s
    _ = (1 + 4 * a) * s ^ 2 + (4 * a + 4 * a ^ 2) := by ring
section
namespace FunctionalInequalities.Energy.SmoothGradient
end FunctionalInequalities.Energy.SmoothGradient
open FunctionalInequalities FunctionalInequalities.Energy FunctionalInequalities.Energy.SmoothGradient
namespace FunctionalInequalities.Energy.SmoothGradient
end FunctionalInequalities.Energy.SmoothGradient
open FunctionalInequalities.Energy.SmoothGradient in
/-- `C4`.  Density for a globally Lipschitz test: the smooth-gradient relaxation of `g` is at most
its raw local-slope energy.  The recovery is by McShane patches with `α = δ = 1 / (n + 1)`. -/
theorem solution (ν : ProbabilityMeasure V) {g : V → ℝ}
    {L : ℝ≥0} (hg : LipschitzWith L g) (hmem : MemLp g 2 (ν : Measure V)) :
    FunctionalInequalities.Energy.SmoothGradient.relaxation ν (hmem.toLp g) ≤ FunctionalInequalities.Energy.LocalSlope.energy ν g := by
  classical
  set E : ℝ≥0∞ := FunctionalInequalities.Energy.LocalSlope.energy ν g with hE
  rcases eq_or_ne E ⊤ with hEtop | hEtop
  · rw [hEtop]; exact le_top
  set a : ℕ → ℝ≥0 := fun n ↦ ((n : ℝ≥0) + 1)⁻¹ with hadef
  have ha0 : ∀ n, 0 < a n := fun n ↦ by
    rw [hadef]
    exact inv_pos.2 (by positivity)
  have ha1 : ∀ n, a n ≤ 1 := by
    intro n
    rw [hadef]
    simp only
    rw [inv_le_one₀ (by positivity)]
    simp
  have hatend : Tendsto (fun n : ℕ ↦ ((a n : ℝ≥0) : ℝ≥0∞)) atTop (𝓝 0) := by
    rw [show (0 : ℝ≥0∞) = ((0 : ℝ≥0) : ℝ≥0∞) from rfl]
    refine ENNReal.tendsto_coe.2 ?_
    rw [← NNReal.tendsto_coe]
    have heq : (fun n : ℕ ↦ ((a n : ℝ≥0) : ℝ)) = fun n : ℕ ↦ ((n : ℝ) + 1)⁻¹ := by
      funext n
      rw [hadef]
      push_cast
      ring
    rw [heq]
    simpa [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  set M : ℝ≥0 := 9 * L + 8 with hM
  have hpatch : ∀ n : ℕ, ∃ (F : V → ℝ) (K : Set V), LipschitzWith (9 * L + 8 * a n) F ∧
      MeasurableSet K ∧ (ν : Measure V) Kᶜ ≤ ((a n : ℝ≥0) : ℝ≥0∞) ∧ (∀ x ∈ K, F x = g x) ∧
      (∀ x, |F x - g x| ≤ 2 * (L : ℝ) + 2 * ((a n : ℝ≥0) : ℝ)) ∧
      ∀ x ∈ K, FunctionalInequalities.Energy.AsymptoticLipschitz.apply F x ≤ FunctionalInequalities.Energy.LocalSlope.apply g x + 2 * ((a n : ℝ≥0) : ℝ≥0∞) :=
    fun n ↦ FunctionalInequalities.Energy.LocalSlope.exists_patch_408915f ν hg (ha0 n) (by exact_mod_cast ha0 n)
  choose F Kset hFlip hKmeas hKmass hFeq hFclose hFslope using hpatch
  -- the patches are `L²(ν)` functions
  have hFmem : ∀ n, MemLp (F n) 2 (ν : Measure V) := by
    intro n
    have hdiff : MemLp (fun x ↦ F n x - g x) 2 (ν : Measure V) := by
      refine MemLp.of_bound ?_ (2 * (L : ℝ) + 2 * ((a n : ℝ≥0) : ℝ)) (ae_of_all _ fun x ↦ ?_)
      · exact (((hFlip n).continuous).sub hg.continuous).aestronglyMeasurable
      · simpa [Real.norm_eq_abs] using hFclose n x
    have hrw : F n = fun x ↦ (F n x - g x) + g x := by funext x; ring
    rw [hrw]
    exact hdiff.add hmem
  -- the energy bound at each patch
  have hMbound : ∀ n, 9 * L + 8 * a n ≤ M := by
    intro n
    rw [hM]
    have : 8 * a n ≤ 8 := by
      calc 8 * a n ≤ 8 * 1 := mul_le_mul_right (ha1 n) 8
        _ = 8 := mul_one 8
    exact add_le_add le_rfl this
  have hmeas_s : Measurable (FunctionalInequalities.Energy.LocalSlope.apply g) := FunctionalInequalities.Energy.LocalSlope.measurable_apply hg.continuous
  have henergy : ∀ n, FunctionalInequalities.Energy.AsymptoticLipschitz.energy ν (F n) ≤
      (1 + 4 * ((a n : ℝ≥0) : ℝ≥0∞)) * E + (4 * ((a n : ℝ≥0) : ℝ≥0∞) +
        4 * ((a n : ℝ≥0) : ℝ≥0∞) ^ 2) + (M : ℝ≥0∞) ^ 2 * ((a n : ℝ≥0) : ℝ≥0∞) := by
    intro n
    set an : ℝ≥0∞ := ((a n : ℝ≥0) : ℝ≥0∞) with handef
    have hpt : ∀ x, FunctionalInequalities.Energy.AsymptoticLipschitz.apply (F n) x ^ 2 ≤
        ((1 + 4 * an) * FunctionalInequalities.Energy.LocalSlope.apply g x ^ 2 + (4 * an + 4 * an ^ 2)) +
          (Kset n)ᶜ.indicator (fun _ ↦ (M : ℝ≥0∞) ^ 2) x := by
      intro x
      by_cases hx : x ∈ Kset n
      · have h1 : FunctionalInequalities.Energy.AsymptoticLipschitz.apply (F n) x ≤ FunctionalInequalities.Energy.LocalSlope.apply g x + 2 * an :=
          hFslope n x hx
        have h2 : FunctionalInequalities.Energy.AsymptoticLipschitz.apply (F n) x ^ 2 ≤
            (FunctionalInequalities.Energy.LocalSlope.apply g x + 2 * an) ^ 2 := pow_le_pow_left' h1 2
        refine h2.trans ?_
        exact le_trans (FunctionalInequalities.Energy.sq_add_two_mul_le _ _) le_self_add
      · have h1 : FunctionalInequalities.Energy.AsymptoticLipschitz.apply (F n) x ≤ (M : ℝ≥0∞) := by
          refine (FunctionalInequalities.Energy.AsymptoticLipschitz.apply_le_of_lipschitzWith (hFlip n) x).trans ?_
          exact_mod_cast hMbound n
        have h2 : FunctionalInequalities.Energy.AsymptoticLipschitz.apply (F n) x ^ 2 ≤ (M : ℝ≥0∞) ^ 2 := pow_le_pow_left' h1 2
        have h3 : (Kset n)ᶜ.indicator (fun _ ↦ (M : ℝ≥0∞) ^ 2) x = (M : ℝ≥0∞) ^ 2 :=
          Set.indicator_of_mem hx _
        rw [h3]
        exact h2.trans le_add_self
    calc FunctionalInequalities.Energy.AsymptoticLipschitz.energy ν (F n)
        ≤ ∫⁻ x, (((1 + 4 * an) * FunctionalInequalities.Energy.LocalSlope.apply g x ^ 2 + (4 * an + 4 * an ^ 2)) +
            (Kset n)ᶜ.indicator (fun _ ↦ (M : ℝ≥0∞) ^ 2) x) ∂(ν : Measure V) :=
          lintegral_mono hpt
      _ = (∫⁻ x, ((1 + 4 * an) * FunctionalInequalities.Energy.LocalSlope.apply g x ^ 2 + (4 * an + 4 * an ^ 2))
            ∂(ν : Measure V)) + (M : ℝ≥0∞) ^ 2 * (ν : Measure V) (Kset n)ᶜ := by
          rw [lintegral_add_right _ ((measurable_const.indicator (hKmeas n).compl)),
            lintegral_indicator_const (hKmeas n).compl]
      _ = ((1 + 4 * an) * E + (4 * an + 4 * an ^ 2)) +
            (M : ℝ≥0∞) ^ 2 * (ν : Measure V) (Kset n)ᶜ := by
          rw [lintegral_add_right _ measurable_const,
            lintegral_const_mul _ (hmeas_s.pow_const 2), lintegral_const, measure_univ, mul_one]
          rfl
      _ ≤ (1 + 4 * an) * E + (4 * an + 4 * an ^ 2) + (M : ℝ≥0∞) ^ 2 * an := by
          exact add_le_add le_rfl (mul_le_mul_right (hKmass n) _)
  -- convergence of the patches in `L²(ν)`
  have hconv : Tendsto (fun n ↦ (hFmem n).toLp (F n)) atTop (𝓝 (hmem.toLp g)) := by
    refine (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun n ↦ F n) hFmem g hmem).mpr ?_
    have hle : ∀ n, eLpNorm (F n - g) 2 (ν : Measure V) ≤
        ‖(2 * (L : ℝ) + 2 : ℝ)‖ₑ * ((a n : ℝ≥0) : ℝ≥0∞) ^ ((1 : ℝ) / 2) := by
      intro n
      have hmono : eLpNorm (F n - g) 2 (ν : Measure V) ≤
          eLpNorm ((Kset n)ᶜ.indicator fun _ ↦ (2 * (L : ℝ) + 2 : ℝ)) 2 (ν : Measure V) := by
        refine eLpNorm_mono fun x ↦ ?_
        by_cases hx : x ∈ Kset n
        · simp [hFeq n x hx]
        · rw [Set.indicator_of_mem hx (fun _ ↦ (2 * (L : ℝ) + 2 : ℝ))]
          have h1 := hFclose n x
          have h2 : 2 * ((a n : ℝ≥0) : ℝ) ≤ 2 := by
            have : ((a n : ℝ≥0) : ℝ) ≤ 1 := by exact_mod_cast ha1 n
            linarith
          have : |F n x - g x| ≤ 2 * (L : ℝ) + 2 := by linarith
          simpa [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * (L : ℝ) + 2)] using this
      refine hmono.trans ?_
      rw [eLpNorm_indicator_const (hKmeas n).compl (by norm_num) (by norm_num)]
      have h2 : ((2 : ℝ≥0∞).toReal) = 2 := by norm_num
      rw [h2]
      exact mul_le_mul_right (ENNReal.rpow_le_rpow (hKmass n) (by norm_num)) _
    have hlim : Tendsto (fun n ↦ ‖(2 * (L : ℝ) + 2 : ℝ)‖ₑ *
        ((a n : ℝ≥0) : ℝ≥0∞) ^ ((1 : ℝ) / 2)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n ↦ ((a n : ℝ≥0) : ℝ≥0∞) ^ ((1 : ℝ) / 2)) atTop (𝓝 0) := by
        have := (ENNReal.continuous_rpow_const (y := (1 : ℝ) / 2)).tendsto 0 |>.comp hatend
        simpa [Function.comp_def, ENNReal.zero_rpow_of_pos (by norm_num : (0:ℝ) < 1 / 2)] using this
      have h2 : Tendsto (fun n ↦ ‖(2 * (L : ℝ) + 2 : ℝ)‖ₑ * ((a n : ℝ≥0) : ℝ≥0∞) ^ ((1 : ℝ) / 2))
          atTop (𝓝 (‖(2 * (L : ℝ) + 2 : ℝ)‖ₑ * 0)) :=
        ENNReal.Tendsto.const_mul h1 (Or.inr (by simp))
      simpa using h2
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun _ ↦ zero_le) hle
  -- lower semicontinuity finishes
  have hlsc := FunctionalInequalities.Energy.le_liminf_of_lowerSemicontinuous (fun f ↦ FunctionalInequalities.Energy.SmoothGradient.relaxation ν f)
    (FunctionalInequalities.Energy.SmoothGradient.preEnergy ν).lowerSemicontinuous_sequentialRelaxation_408915f hconv
  refine hlsc.trans ?_
  set C : ℝ≥0∞ := 4 * E + 8 + (M : ℝ≥0∞) ^ 2 with hC
  have hCtop : C ≠ ⊤ := by
    rw [hC]
    refine ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨?_, by norm_num⟩, ?_⟩
    · exact ENNReal.mul_ne_top (by norm_num) hEtop
    · exact ENNReal.pow_ne_top ENNReal.coe_ne_top
  have hstep : ∀ n, FunctionalInequalities.Energy.SmoothGradient.relaxation ν ((hFmem n).toLp (F n)) ≤ E + ((a n : ℝ≥0) : ℝ≥0∞) * C := by
    intro n
    set an : ℝ≥0∞ := ((a n : ℝ≥0) : ℝ≥0∞) with handef
    have han1 : an ≤ 1 := by rw [handef]; exact_mod_cast ha1 n
    refine le_trans
      (FunctionalInequalities.Energy.SmoothGradient.relaxation_le_asymptoticLipschitz_of_lipschitzWith_408915f ν (hFlip n) (hFmem n)) ?_
    refine (henergy n).trans ?_
    have hsq : an ^ 2 ≤ an := by
      calc an ^ 2 = an * an := sq an
        _ ≤ an * 1 := mul_le_mul_right han1 an
        _ = an := mul_one an
    calc (1 + 4 * an) * E + (4 * an + 4 * an ^ 2) + (M : ℝ≥0∞) ^ 2 * an
        = E + 4 * an * E + (4 * an + 4 * an ^ 2) + (M : ℝ≥0∞) ^ 2 * an := by ring
      _ ≤ E + 4 * an * E + (4 * an + 4 * an) + (M : ℝ≥0∞) ^ 2 * an := by gcongr
      _ = E + an * (4 * E + 8 + (M : ℝ≥0∞) ^ 2) := by ring
  refine le_trans (liminf_le_liminf (Eventually.of_forall hstep)) ?_
  have htend : Tendsto (fun n ↦ E + ((a n : ℝ≥0) : ℝ≥0∞) * C) atTop (𝓝 E) := by
    have h1 : Tendsto (fun n ↦ ((a n : ℝ≥0) : ℝ≥0∞) * C) atTop (𝓝 0) := by
      have := ENNReal.Tendsto.mul_const hatend (Or.inr hCtop)
      simpa using this
    simpa using tendsto_const_nhds.add h1
  exact le_of_eq htend.liminf_eq
