-- Prove2me | solution 1 for FunctionalInequalities.Poincare.SmoothTest.tendsto_energy_scaled_mul_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T17:42:57.320895+00:00
-- url     : https://prove2.me/submissions/aa212fdf-941c-4160-b232-2ff3b6f8b633

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_SmoothTest_Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Moments.Variance
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Theorems.Thm_FunctionalInequalities_Poincare_SmoothTest_norm_gradient_scaled_mul_sq_le_408915f

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Poincare
end FunctionalInequalities.Poincare
open FunctionalInequalities FunctionalInequalities.Poincare
section
namespace FunctionalInequalities.Poincare.SmoothTest
end FunctionalInequalities.Poincare.SmoothTest
open FunctionalInequalities FunctionalInequalities.Poincare FunctionalInequalities.Poincare.SmoothTest
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]
section Cutoff
variable [FiniteDimensional ℝ E]
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Inside the ball the cutoff does not change the gradient. -/
theorem FunctionalInequalities.Poincare.SmoothTest.norm_gradient_scaled_mul_sq_eq {R : ℝ} (hR : 0 < R) {f : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hx : ‖x‖ < R) :
    ‖gradient (fun y => Energy.Euclidean.LipschitzApproximation.scaled R y * f y) x‖ ^ 2 =
      ‖gradient f x‖ ^ 2 := by
    rw [Energy.Euclidean.LipschitzApproximation.gradient_scaled_mul hf,
      Energy.Euclidean.LipschitzApproximation.scaled_eq_one hR hx.le]
    have h0 : gradient (Energy.Euclidean.LipschitzApproximation.scaled R) x = 0 := by
      unfold gradient
      rw [Energy.Euclidean.LipschitzApproximation.fderiv_scaled_eq_zero hR hx]
      simp
    rw [h0]
    simp
namespace FunctionalInequalities.Poincare.SmoothTest
end FunctionalInequalities.Poincare.SmoothTest
open FunctionalInequalities.Poincare.SmoothTest in
/-- The energies of the cutoffs `f χ_{n+1}` converge to the energy of `f` for an admissible `f`. -/
theorem solution {μ : Measure E} [IsFiniteMeasure μ] {f : E → ℝ}
    (hf : FunctionalInequalities.Poincare.SmoothTest.Admissible μ f) :
    Tendsto (fun n : ℕ =>
        FunctionalInequalities.Poincare.SmoothTest.energy μ (fun x => FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled ((n : ℝ) + 1) x * f x))
      atTop (𝓝 (FunctionalInequalities.Poincare.SmoothTest.energy μ f)) := by
    unfold FunctionalInequalities.Poincare.SmoothTest.energy
    obtain ⟨M, hM0, hM⟩ :=
      FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.exists_bound_fderiv_bump (E := E)
    have hsq : Integrable (fun x : E => f x ^ 2) μ :=
      (memLp_two_iff_integrable_sq hf.memLp_two.1).1 hf.memLp_two
    have hbound :
        Integrable
          (fun x : E => 2 * ‖gradient f x‖ ^ 2 + 2 * M ^ 2 * f x ^ 2) μ :=
      (hf.energy_integrable.const_mul 2).add (hsq.const_mul (2 * M ^ 2))
    have hmeas :
        ∀ n : ℕ, AEStronglyMeasurable
          (fun x : E =>
            ‖gradient
                (fun y =>
                  FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled ((n : ℝ) + 1) y *
                    f y) x‖ ^ 2) μ := by
      intro n
      let g : E → ℝ :=
        fun y =>
          FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled ((n : ℝ) + 1) y * f y
      have hg : ContDiff ℝ ∞ g := by
        dsimp [g]
        exact
          (FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.contDiff_scaled
            ((n : ℝ) + 1)).mul hf.smooth'
      have hgf : Continuous (fderiv ℝ g) :=
        hg.continuous_fderiv (by simp)
      have hgrad : Continuous (gradient g) := by
        change
          Continuous
            (fun x => (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ g x))
        exact (InnerProductSpace.toDual ℝ E).symm.continuous.comp hgf
      have hc : Continuous (fun x => ‖gradient g x‖ ^ 2) :=
        (hgrad.norm).pow 2
      exact hc.aestronglyMeasurable
    have hdom :
        ∀ n : ℕ, ∀ᵐ x ∂μ,
          ‖‖gradient
              (fun y =>
                FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled ((n : ℝ) + 1) y *
                  f y) x‖ ^ 2‖ ≤
            2 * ‖gradient f x‖ ^ 2 + 2 * M ^ 2 * f x ^ 2 := by
      intro n
      filter_upwards [] with x
      have hR : 0 < (n : ℝ) + 1 := by positivity
      have hfd : DifferentiableAt ℝ f x :=
        (hf.smooth'.differentiable (by simp)) x
      have hi := FunctionalInequalities.Poincare.SmoothTest.norm_gradient_scaled_mul_sq_le_408915f
        (f := f) (R := (n : ℝ) + 1) hR hM hfd
      have hdiv : M / ((n : ℝ) + 1) ≤ M := by
        exact div_le_self hM0 (by linarith)
      have hnonneg : 0 ≤ M / ((n : ℝ) + 1) := by
        exact div_nonneg hM0 (le_of_lt hR)
      have hsqdiv :
          (M / ((n : ℝ) + 1)) ^ 2 ≤ M ^ 2 := by
        have h := mul_self_le_mul_self hnonneg hdiv
        simpa [pow_two] using h
      have hi' :
          ‖gradient
              (fun y =>
                FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled ((n : ℝ) + 1) y *
                  f y) x‖ ^ 2 ≤
            2 * ‖gradient f x‖ ^ 2 + 2 * M ^ 2 * f x ^ 2 := by
        calc
          ‖gradient
              (fun y =>
                FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled ((n : ℝ) + 1) y *
                  f y) x‖ ^ 2 ≤
              2 * ‖gradient f x‖ ^ 2 +
                2 * (M / ((n : ℝ) + 1)) ^ 2 * f x ^ 2 := hi
          _ ≤ 2 * ‖gradient f x‖ ^ 2 + 2 * M ^ 2 * f x ^ 2 := by
            gcongr
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hi'
    have hlim :
        ∀ᵐ x ∂μ,
          Tendsto
            (fun n : ℕ =>
              ‖gradient
                  (fun y =>
                    FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled ((n : ℝ) + 1) y *
                      f y) x‖ ^ 2)
            atTop (𝓝 (‖gradient f x‖ ^ 2)) := by
      filter_upwards [] with x
      refine tendsto_atTop_of_eventually_const (i₀ := Nat.ceil ‖x‖) ?_
      intro n hn
      have hceil : ‖x‖ ≤ (Nat.ceil ‖x‖ : ℝ) := by
        exact Nat.le_ceil _
      have hn' : (Nat.ceil ‖x‖ : ℝ) ≤ n := by
        exact_mod_cast hn
      have hx : ‖x‖ < (n : ℝ) + 1 := by
        linarith
      have hR : 0 < (n : ℝ) + 1 := by positivity
      have hfd : DifferentiableAt ℝ f x :=
        (hf.smooth'.differentiable (by simp)) x
      exact
        FunctionalInequalities.Poincare.SmoothTest.norm_gradient_scaled_mul_sq_eq
          (f := f) (R := (n : ℝ) + 1) hR hfd hx
    exact
      MeasureTheory.tendsto_integral_of_dominated_convergence
        (fun x : E => 2 * ‖gradient f x‖ ^ 2 + 2 * M ^ 2 * f x ^ 2)
        hmeas hbound hdom hlim
