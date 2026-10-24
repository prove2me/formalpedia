-- Prove2me | solution 1 for FunctionalInequalities.Analysis.BakryEmery.integral_inner_fderiv_gradient_tilted_eq_integral_fderiv_mul_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T14:48:01.679926+00:00
-- url     : https://prove2.me/submissions/b841da8f-8cb1-4dd4-8f8a-b595272c26b6

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Bochner_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Gamma
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_WeakDerivative_Basic
import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.Topology.MetricSpace.Lipschitz
import Theorems.Thm_FunctionalInequalities_Analysis_hasWeakDerivAlong_of_lipschitz_408915f

section
noncomputable section
open MeasureTheory Filter Topology
open scoped ContDiff ENNReal
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Energy
end FunctionalInequalities.Energy
open FunctionalInequalities FunctionalInequalities.Energy
section
namespace FunctionalInequalities.Energy.Euclidean
end FunctionalInequalities.Energy.Euclidean
open FunctionalInequalities FunctionalInequalities.Energy FunctionalInequalities.Energy.Euclidean
section
namespace FunctionalInequalities.Energy.Euclidean.LipschitzApproximation
end FunctionalInequalities.Energy.Euclidean.LipschitzApproximation
open FunctionalInequalities FunctionalInequalities.Energy FunctionalInequalities.Energy.Euclidean FunctionalInequalities.Energy.Euclidean.LipschitzApproximation
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
section FiniteDimensional
variable [FiniteDimensional ℝ E]
theorem FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.hasCompactSupport_scaled {R : ℝ} (hR : 0 < R) :
    HasCompactSupport (scaled (E := E) R) :=
  HasCompactSupport.intro (isCompact_closedBall (0 : E) (2 * R)) fun x hx =>
    scaled_eq_zero hR (by
      rw [Metric.mem_closedBall, dist_zero_right] at hx
      exact le_of_lt (not_le.mp hx))
end FiniteDimensional
end
end
end
end
end
end

noncomputable section
open MeasureTheory Filter Topology
open FunctionalInequalities.Energy.Euclidean.LipschitzApproximation
open scoped RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section
namespace FunctionalInequalities.Analysis.BakryEmery
end FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Analysis.BakryEmery
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
namespace FunctionalInequalities.Analysis.BakryEmery
end FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.BakryEmery in
set_option maxHeartbeats 800000 in
/-- **Mean Hessian identity for a `C¹` potential with Lipschitz gradient** (Letwin
arXiv:2607.24164v1, Lemma 2.3, analytic part, at `C^{1,1}`; weak Letwin route):
`∫ ⟪D(∇φ)(x) u, v⟫ dν = ∫ ∂_uφ ∂_vφ dν` for convex `φ ∈ C¹` with `G`-Lipschitz gradient,
`e^{-φ}` a probability density and `∇φ ∈ L²(ν)`, where `D(∇φ)` is the a.e. (Rademacher)
derivative of the Lipschitz map `∇φ`. -/
theorem solution (φ : E → ℝ)
    (hφ : ContDiff ℝ 1 φ) {G : NNReal} (hG : LipschitzWith G (gradient φ))
    (hc : ConvexOn ℝ Set.univ φ)
    (hexp : Integrable (fun x => Real.exp (-φ x)) (volume : Measure E))
    (hnorm : ∫ x, Real.exp (-φ x) ∂(volume : Measure E) = 1)
    (hgrad : MemLp (gradient φ) 2 ((volume : Measure E).tilted (-φ))) (u v : E) :
    (∫ x, ⟪fderiv ℝ (gradient φ) x u, v⟫ ∂((volume : Measure E).tilted (-φ))) =
      ∫ x, fderiv ℝ φ x u * fderiv ℝ φ x v ∂((volume : Measure E).tilted (-φ)) := by
  have _hconvex := hc
  let μ : Measure E := (volume : Measure E).tilted (-φ)
  let _ : IsProbabilityMeasure μ := isProbabilityMeasure_tilted hexp
  let f : E → ℝ := fun x => ⟪gradient φ x, v⟫
  let g : E → ℝ := fun x => fderiv ℝ f x u
  let p : E → ℝ := fun x => fderiv ℝ φ x u * f x
  have hfLip : LipschitzWith ((G : ℝ) * ‖v‖).toNNReal f := by
    dsimp only [f]
    apply LipschitzWith.of_dist_le'
    intro x y
    rw [dist_eq_norm, ← inner_sub_left]
    have hi := norm_inner_le_norm (𝕜 := ℝ) (gradient φ x - gradient φ y) v
    have hg := mul_le_mul_of_nonneg_right (hG.dist_le_mul x y) (norm_nonneg v)
    rw [dist_eq_norm] at hg
    nlinarith
  have hf2 : MemLp f 2 μ := hgrad.inner_const (𝕜 := ℝ) v
  have hf1 : Integrable f μ := hf2.integrable (by norm_num)
  have hu2 : MemLp (fun x => fderiv ℝ φ x u) 2 μ := by
    simpa only [inner_gradient_left] using hgrad.inner_const (𝕜 := ℝ) u
  have hp : Integrable p μ := hu2.integrable_mul hf2
  have hgmeas : Measurable g :=
    (show Continuous (fun A : E →L[ℝ] ℝ => A u) from
      continuous_id.clm_apply continuous_const).measurable.comp (measurable_fderiv ℝ f)
  have hg : Integrable g μ := by
    apply (integrable_const
      ((((G : ℝ) * ‖v‖).toNNReal : ℝ) * ‖u‖)).mono' hgmeas.aestronglyMeasurable
    exact ae_of_all _ fun x =>
      ((fderiv ℝ f x).le_opNorm u).trans
        (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hfLip) (norm_nonneg u))
  have hgeq : g =ᵐ[μ] fun x => ⟪fderiv ℝ (gradient φ) x u, v⟫ := by
    have hdiff : ∀ᵐ x : E ∂(volume : Measure E), DifferentiableAt ℝ (gradient φ) x :=
      hG.ae_differentiableAt
    have hdiffμ : ∀ᵐ x : E ∂μ, DifferentiableAt ℝ (gradient φ) x :=
      (tilted_absolutelyContinuous (volume : Measure E) (-φ)).ae_le hdiff
    filter_upwards [hdiffμ] with x hx
    dsimp only [g, f]
    simpa using fderiv_inner_apply ℝ hx (differentiableAt_const v) u

  have hscaledNorm (R : ℝ) (x : E) : ‖FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled R x‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled_nonneg R x)]
    exact FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled_le_one R x
  have hcut (k : E → ℝ) (hk : Integrable k μ) (R : ℝ) :
      Integrable (fun x => FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled R x * k x) μ := by
    refine hk.norm.mono'
      ((FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.continuous_scaled R).aestronglyMeasurable.mul hk.aestronglyMeasurable) ?_
    filter_upwards [] with x
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hscaledNorm R x)
  have hevent (x : E) : ∀ᶠ n : ℕ in atTop, ‖x‖ < (n : ℝ) + 1 := by
    obtain ⟨N, hN⟩ := exists_nat_ge ‖x‖
    apply Filter.eventually_atTop.mpr
    refine ⟨N, fun n hn => ?_⟩
    exact lt_of_le_of_lt (hN.trans (Nat.cast_le.mpr hn)) (lt_add_one _)
  have hcutLim (k : E → ℝ) (hk : Integrable k μ) :
      Tendsto (fun n : ℕ => ∫ x, FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled ((n : ℝ) + 1) x * k x ∂μ)
        atTop (𝓝 (∫ x, k x ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => ‖k x‖)
      (fun n => (hcut k hk ((n : ℝ) + 1)).aestronglyMeasurable) hk.norm
    · intro n
      filter_upwards [] with x
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hscaledNorm _ x)
    · filter_upwards [] with x
      have heq : (fun n : ℕ => FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled ((n : ℝ) + 1) x * k x) =ᶠ[atTop]
          fun _ => k x := by
        filter_upwards [hevent x] with n hn
        rw [FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled_eq_one (by positivity) hn.le, one_mul]
      exact tendsto_const_nhds.congr' heq.symm

  obtain ⟨M, hM0, hM⟩ := FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.exists_bound_fderiv_bump (E := E)
  have hcof (n : ℕ) (x : E) :
      ‖fderiv ℝ (FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled ((n : ℝ) + 1)) x u‖ ≤ M * ‖u‖ := by
    have hR : 0 < (n : ℝ) + 1 := by positivity
    have hi : ((n : ℝ) + 1)⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ (by
        have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith)
    have hd : ‖fderiv ℝ (FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled ((n : ℝ) + 1)) x‖ ≤ M :=
      (FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.norm_fderiv_scaled_le hR hM x).trans
        (mul_le_of_le_one_left hM0 hi)
    exact ((fderiv ℝ (FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled ((n : ℝ) + 1)) x).le_opNorm u).trans
      (mul_le_mul_of_nonneg_right hd (norm_nonneg u))
  have herrMeas (n : ℕ) :
      AEStronglyMeasurable
        (fun x => fderiv ℝ (FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled ((n : ℝ) + 1)) x u * f x) μ :=
    (((FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.contDiff_scaled ((n : ℝ) + 1)).continuous_fderiv (by simp)).clm_apply
      continuous_const).aestronglyMeasurable.mul hf1.aestronglyMeasurable
  have herrBound (n : ℕ) (x : E) :
      ‖fderiv ℝ (FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled ((n : ℝ) + 1)) x u * f x‖ ≤
        (M * ‖u‖) * ‖f x‖ := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hcof n x) (norm_nonneg _)
  have herrInt (n : ℕ) :
      Integrable (fun x => fderiv ℝ (FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled ((n : ℝ) + 1)) x u * f x) μ :=
    (hf1.norm.const_mul (M * ‖u‖)).mono' (herrMeas n) (ae_of_all _ (herrBound n))
  have herrLim :
      Tendsto (fun n : ℕ =>
        ∫ x, fderiv ℝ (FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled ((n : ℝ) + 1)) x u * f x ∂μ) atTop (𝓝 0) := by
    have ht :
        Tendsto (fun n : ℕ =>
          ∫ x, fderiv ℝ (FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled ((n : ℝ) + 1)) x u * f x ∂μ)
          atTop (𝓝 (∫ _x : E, (0 : ℝ) ∂μ)) := by
      apply tendsto_integral_of_dominated_convergence
        (fun x => (M * ‖u‖) * ‖f x‖) herrMeas
        (hf1.norm.const_mul (M * ‖u‖))
      · exact fun n => ae_of_all _ (herrBound n)
      · filter_upwards [] with x
        have heq : (fun n : ℕ =>
            fderiv ℝ (FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled ((n : ℝ) + 1)) x u * f x) =ᶠ[atTop]
            fun _ => (0 : ℝ) := by
          filter_upwards [hevent x] with n hn
          rw [FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.fderiv_scaled_eq_zero (by positivity) hn]
          simp only [zero_apply, zero_mul]
        exact tendsto_const_nhds.congr' heq.symm
    simpa only [integral_zero] using ht

  have htilt (k : E → ℝ) :
      (∫ x, k x ∂μ) = ∫ x, Real.exp (-φ x) * k x ∂(volume : Measure E) := by
    change (∫ x, k x ∂((volume : Measure E).tilted (-φ))) = _
    rw [integral_tilted]
    simp only [Pi.neg_apply, hnorm, div_one, smul_eq_mul]
  have hidentity (n : ℕ) :
      (∫ x, FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled ((n : ℝ) + 1) x * g x ∂μ) =
        (∫ x, FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled ((n : ℝ) + 1) x * p x ∂μ) -
          ∫ x, fderiv ℝ (FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled ((n : ℝ) + 1)) x u * f x ∂μ := by
    let R : ℝ := (n : ℝ) + 1
    have hR : 0 < R := by dsimp only [R]; positivity
    have hχ : ContDiff ℝ 1 (FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled (E := E) R) :=
      (FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.contDiff_scaled R).of_le (by simp)
    have hd (x : E) :
        fderiv ℝ (fun y => FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled R y * Real.exp (-φ y)) x u =
          Real.exp (-φ x) * fderiv ℝ (FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled R) x u -
            Real.exp (-φ x) * FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled R x * fderiv ℝ φ x u := by
      have hd' : HasFDerivAt (fun y => FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled R y * Real.exp (-φ y))
          (FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled R x • (Real.exp (-φ x) • -fderiv ℝ φ x) +
            Real.exp (-φ x) • fderiv ℝ (FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled R) x) x :=
        (hχ.differentiable one_ne_zero x).hasFDerivAt.mul
          ((hφ.differentiable one_ne_zero x).hasFDerivAt.neg.exp)
      rw [hd'.fderiv]
      simp only [add_apply, smul_apply, neg_apply, smul_eq_mul]
      ring
    have hw := (FunctionalInequalities.Analysis.hasWeakDerivAlong_of_lipschitz_408915f hfLip u).2.2
      (fun x => FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled R x * Real.exp (-φ x))
      (hχ.mul hφ.neg.exp) (FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.hasCompactSupport_scaled hR).mul_right
    have he :
        (∫ x, (fderiv ℝ (FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled R) x u * f x - FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled R x * p x) ∂μ) =
          -(∫ x, FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled R x * g x ∂μ) := by
      calc
        _ = ∫ x, Real.exp (-φ x) *
            (fderiv ℝ (FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled R) x u * f x - FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled R x * p x)
              ∂(volume : Measure E) := htilt _
        _ = ∫ x, f x *
            fderiv ℝ (fun y => FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled R y * Real.exp (-φ y)) x u
              ∂(volume : Measure E) := by
          apply integral_congr_ae
          filter_upwards [] with x
          rw [hd x]
          dsimp only [p]
          ring
        _ = -(∫ x, g x * (FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled R x * Real.exp (-φ x))
              ∂(volume : Measure E)) := hw
        _ = -(∫ x, FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled R x * g x ∂μ) := by
          rw [htilt]
          congr 1
          apply integral_congr_ae
          filter_upwards [] with x
          ring
    rw [integral_sub (herrInt n) (hcut p hp R)] at he
    change (∫ x, FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled R x * g x ∂μ) =
      (∫ x, FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled R x * p x ∂μ) -
        ∫ x, fderiv ℝ (FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled R) x u * f x ∂μ
    linarith only [he]
  have hlimits := (hcutLim p hp).sub herrLim
  have heq :
      (fun n : ℕ => (∫ x, FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled ((n : ℝ) + 1) x * p x ∂μ) -
        ∫ x, fderiv ℝ (FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled ((n : ℝ) + 1)) x u * f x ∂μ) =
      (fun n : ℕ => ∫ x, FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled ((n : ℝ) + 1) x * g x ∂μ) :=
    funext fun n => (hidentity n).symm
  rw [heq] at hlimits
  have hmean : (∫ x, g x ∂μ) = ∫ x, p x ∂μ := by
    simpa only [sub_zero] using tendsto_nhds_unique (hcutLim g hg) hlimits
  calc
    (∫ x, ⟪fderiv ℝ (gradient φ) x u, v⟫ ∂μ) =
        ∫ x, g x ∂μ := integral_congr_ae hgeq.symm
    _ = ∫ x, p x ∂μ := hmean
    _ = ∫ x, fderiv ℝ φ x u * fderiv ℝ φ x v ∂μ := by
      simp only [p, f, inner_gradient_left]
