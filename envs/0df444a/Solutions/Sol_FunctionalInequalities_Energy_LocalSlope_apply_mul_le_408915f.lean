-- Prove2me | solution 1 for FunctionalInequalities.Energy.LocalSlope.apply_mul_le_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:52:30.977225+00:00
-- url     : https://prove2.me/submissions/d021d1d2-f6cf-469b-b892-71d0991a7526

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
/-- A uniform bound on the secant quotients bounds the secant supremum. -/
theorem FunctionalInequalities.Energy.LocalSlope.secant_le_of_forall {f : X → ℝ} {r : ℝ} {x : X} {c : ℝ≥0∞}
    (h : ∀ y, dist y x < r → ENNReal.ofReal (dist (f y) (f x) / dist y x) ≤ c) :
    secant f r x ≤ c :=
  iSup_le fun y ↦ iSup_le fun hy ↦ h y hy
/-- A real Lipschitz-type bound on a ball bounds the secant supremum. -/
theorem FunctionalInequalities.Energy.LocalSlope.secant_le_ofReal {f : X → ℝ} {r : ℝ} {x : X} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ y, dist y x < r → dist (f y) (f x) ≤ c * dist y x) :
    secant f r x ≤ ENNReal.ofReal c := by
  refine secant_le_of_forall fun y hy ↦ ENNReal.ofReal_le_ofReal ?_
  rcases eq_or_lt_of_le (dist_nonneg (x := y) (y := x)) with h0 | h0
  · simp [← h0, hc]
  · exact (div_le_iff₀ h0).2 (h y hy)
/-- A bound on the secant supremum is a Lipschitz-type bound on the ball. -/
theorem FunctionalInequalities.Energy.LocalSlope.dist_le_of_secant_le {f : X → ℝ} {r : ℝ} {x : X} {c : ℝ} (hc : 0 ≤ c)
    (h : secant f r x ≤ ENNReal.ofReal c) {y : X} (hy : dist y x < r) :
    dist (f y) (f x) ≤ c * dist y x := by
  rcases eq_or_lt_of_le (dist_nonneg (x := y) (y := x)) with h0 | h0
  · have : y = x := by simpa [eq_comm] using h0.symm
    simp [this]
  · have hq : ENNReal.ofReal (dist (f y) (f x) / dist y x) ≤ ENNReal.ofReal c :=
      le_trans (le_iSup₂_of_le y hy le_rfl) h
    rw [ENNReal.ofReal_le_ofReal_iff hc, div_le_iff₀ h0] at hq
    exact hq
/-- Below any strict upper bound for the local slope there is a radius whose secant supremum
already respects it. -/
theorem FunctionalInequalities.Energy.LocalSlope.exists_secant_le {f : X → ℝ} {x : X} {c : ℝ≥0∞} (h : apply f x < c) :
    ∃ r : ℝ, 0 < r ∧ secant f r x ≤ c := by
  rw [apply_eq_iInf_secant, iInf_lt_iff] at h
  obtain ⟨r, hr⟩ := h
  rw [iInf_lt_iff] at hr
  obtain ⟨hr0, hlt⟩ := hr
  exact ⟨r, hr0, hlt.le⟩
end Metric
end
section
namespace FunctionalInequalities.Energy.LocalSlope
end FunctionalInequalities.Energy.LocalSlope
open FunctionalInequalities FunctionalInequalities.Energy FunctionalInequalities.Energy.LocalSlope
section Leibniz
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
namespace FunctionalInequalities.Energy.LocalSlope
end FunctionalInequalities.Energy.LocalSlope
open FunctionalInequalities.Energy.LocalSlope in
omit [InnerProductSpace ℝ V] in
/-- the local-slope product bound.  Multiplying by a bounded `N`-Lipschitz factor costs at most `|g x| · N` in the local
slope.  Here the moving point is only `y`, so no correction in the radius is needed. -/
theorem solution (g h : V → ℝ) {N : ℝ≥0} (hh : LipschitzWith N h)
    (hh1 : ∀ y, |h y| ≤ 1) (x : V) :
    FunctionalInequalities.Energy.LocalSlope.apply (fun y ↦ g y * h y) x ≤ FunctionalInequalities.Energy.LocalSlope.apply g x + ENNReal.ofReal |g x| * N := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε hlt ↦ ?_
  have hA : FunctionalInequalities.Energy.LocalSlope.apply g x ≠ ⊤ := by
    intro htop
    rw [htop] at hlt
    simp at hlt
  set a : ℝ := (FunctionalInequalities.Energy.LocalSlope.apply g x).toReal with ha
  have ha0 : 0 ≤ a := ENNReal.toReal_nonneg
  have haA : FunctionalInequalities.Energy.LocalSlope.apply g x = ENNReal.ofReal a := (ENNReal.ofReal_toReal hA).symm
  have hεr : (0 : ℝ) < (ε : ℝ) := hε
  have hstep : FunctionalInequalities.Energy.LocalSlope.apply g x < ENNReal.ofReal (a + (ε : ℝ)) := by
    rw [haA, ENNReal.ofReal_lt_ofReal_iff (by positivity)]
    linarith
  obtain ⟨r, hr0, hsec⟩ := FunctionalInequalities.Energy.LocalSlope.exists_secant_le hstep
  have hkey : ∀ y : V, dist y x < r →
      dist (g y * h y) (g x * h x) ≤ (a + (ε : ℝ) + |g x| * N) * dist y x := by
    intro y hy
    have hgyx : dist (g y) (g x) ≤ (a + (ε : ℝ)) * dist y x :=
      FunctionalInequalities.Energy.LocalSlope.dist_le_of_secant_le (by positivity) hsec hy
    have hhyx : |h y - h x| ≤ (N : ℝ) * dist y x := by
      simpa [Real.dist_eq] using hh.dist_le_mul y x
    have hexp : g y * h y - g x * h x = (g y - g x) * h y + g x * (h y - h x) := by ring
    have h1 : |(g y - g x) * h y| ≤ (a + (ε : ℝ)) * dist y x := by
      rw [abs_mul]
      calc |g y - g x| * |h y| ≤ ((a + (ε : ℝ)) * dist y x) * 1 := by
            refine mul_le_mul (by simpa [Real.dist_eq] using hgyx) (hh1 y) (abs_nonneg _) ?_
            positivity
        _ = (a + (ε : ℝ)) * dist y x := by ring
    have h2 : |g x * (h y - h x)| ≤ |g x| * ((N : ℝ) * dist y x) := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hhyx (abs_nonneg _)
    calc dist (g y * h y) (g x * h x) = |(g y - g x) * h y + g x * (h y - h x)| := by
          rw [Real.dist_eq, hexp]
      _ ≤ |(g y - g x) * h y| + |g x * (h y - h x)| := abs_add_le _ _
      _ ≤ (a + (ε : ℝ)) * dist y x + |g x| * ((N : ℝ) * dist y x) := add_le_add h1 h2
      _ = (a + (ε : ℝ) + |g x| * N) * dist y x := by ring
  refine (FunctionalInequalities.Energy.LocalSlope.apply_le_secant _ hr0 x).trans ?_
  refine (FunctionalInequalities.Energy.LocalSlope.secant_le_ofReal (by positivity) hkey).trans ?_
  rw [ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_add ha0 (by positivity), ← haA,
    ENNReal.ofReal_mul (abs_nonneg (g x)), ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_coe_nnreal]
  exact le_of_eq (by ring)
