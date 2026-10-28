-- Prove2me | solution 1 for FunctionalInequalities.Analysis.BakryEmery.mul_integral_gamma_le_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:26:54.057959+00:00
-- url     : https://prove2.me/submissions/ae108690-9b33-48d3-aa91-fd00cdc91f15

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Gamma
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Bochner_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Curvature
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_gammaTwo_eq_hessianSqStdBasis_add_readable
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_integrable_gamma_weightedLaplacian_readable
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_integrable_weightedLaplacian_gamma_readable
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_integral_gamma_weightedLaplacian_eq_readable

section
noncomputable section
open InnerProductSpace
open scoped ContDiff RealInnerProductSpace
section
universe u
section DifferentialTools
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
section Gradient
variable [CompleteSpace E]
/-- The gradient of a `C^n` function is `C^m` when `m + 1 ≤ n`. -/
theorem FunctionalInequalities.Analysis.BakryEmery.contDiff_gradient {f : E → ℝ} {n m : WithTop ℕ∞} (hf : ContDiff ℝ n f) (hmn : m + 1 ≤ n) :
    ContDiff ℝ m (gradient f) :=
  (toDual ℝ E).symm.contDiff.comp (hf.fderiv_right hmn)
end Gradient
end DifferentialTools
end
end
end

section
noncomputable section
open InnerProductSpace
open scoped ContDiff RealInnerProductSpace
section
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
section Gamma
variable [CompleteSpace E]
theorem FunctionalInequalities.Analysis.BakryEmery.gamma_apply (f g : E → ℝ) (x : E) : gamma f g x = ⟪gradient f x, gradient g x⟫ := rfl
/-- `Γ(f, f) = ‖∇f‖²`: the normalisation of `Γ` carries no extra factor. -/
theorem FunctionalInequalities.Analysis.BakryEmery.gamma_self (f : E → ℝ) (x : E) : gamma f f x = ‖gradient f x‖ ^ 2 :=
  real_inner_self_eq_norm_sq _
/-- Regularity of the carré du champ: `C^{n+1}` data give a `C^n` carré du champ. -/
theorem FunctionalInequalities.Analysis.BakryEmery.contDiff_gamma {n p q : WithTop ℕ∞} {f g : E → ℝ} (hf : ContDiff ℝ p f)
    (hg : ContDiff ℝ q g) (hp : n + 1 ≤ p) (hq : n + 1 ≤ q) : ContDiff ℝ n (gamma f g) :=
  ContDiff.inner ℝ (contDiff_gradient hf hp) (contDiff_gradient hg hq)
/-- The carré du champ inherits the compact support of its first argument. -/
theorem FunctionalInequalities.Analysis.BakryEmery.hasCompactSupport_gamma_left {f : E → ℝ} (g : E → ℝ) (hfc : HasCompactSupport f) :
    HasCompactSupport (gamma f g) := by
  refine (hasCompactSupport_gradient hfc).mono fun x hx => ?_
  intro h0
  apply hx
  simp [gamma_apply, h0]
variable [FiniteDimensional ℝ E]
theorem FunctionalInequalities.Analysis.BakryEmery.gammaTwo_apply (U f : E → ℝ) (x : E) :
    gammaTwo U f x =
      weightedLaplacian U (fun y => gamma f f y) x / 2 - gamma f (weightedLaplacian U f) x := rfl
end Gamma
end
end
end

section
noncomputable section
open InnerProductSpace
open scoped ContDiff RealInnerProductSpace
section
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
section HessianSq
variable [FiniteDimensional ℝ E]
theorem FunctionalInequalities.Analysis.BakryEmery.hessianSqStdBasis_nonneg (f : E → ℝ) (x : E) : 0 ≤ hessianSqStdBasis f x :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
end HessianSq
end
end
end

noncomputable section
open MeasureTheory InnerProductSpace
open scoped ContDiff RealInnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
/-- Pointwise `CD(ρ, ∞)`: if `∇∇U ≥ ρ`, then `ρ Γ(f) ≤ Γ₂(f)` for every `C³` function `f`. -/
theorem FunctionalInequalities.Analysis.BakryEmery.mul_gamma_le_gammaTwo {U f : E → ℝ} (hU : ContDiff ℝ 2 U) (hf : ContDiff ℝ 3 f) {ρ : ℝ}
    (hH : ∀ x v, ρ * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ U x v v) (x : E) :
    ρ * gamma f f x ≤ gammaTwo U f x := by
  rw [gammaTwo_eq_hessianSqStdBasis_add_readable hU hf x, gamma_self]
  have hH' := hH x (gradient f x)
  have hnonneg := hessianSqStdBasis_nonneg f x
  linarith
variable [MeasurableSpace E] [BorelSpace E] (m : MeasureTheory.Measure E) [m.IsAddHaarMeasure]
/-- The invariance `∫ ℒ Γ(f) dμ = 0` for `μ = m.tilted (-U)`. -/
theorem FunctionalInequalities.Analysis.BakryEmery.integral_weightedLaplacian_gamma_eq_zero {U f : E → ℝ} (hU : ContDiff ℝ 2 U)
    (hf : ContDiff ℝ 3 f) (hfc : HasCompactSupport f) :
    ∫ x, weightedLaplacian U (fun y => gamma f f y) x ∂(m.tilted (-U)) = 0 := by
  have h :=
    integral_inner_gradient_tilted m
      (U := U) (f := fun y => gamma f f y) (g := fun _ : E => (1 : ℝ))
      (hU.of_le (by norm_num))
      (contDiff_gamma (n := 2) hf hf (by norm_num) (by norm_num))
      (hasCompactSupport_gamma_left f hfc)
      (contDiff_const (c := (1 : ℝ)))
  simp only [gradient_fun_const, inner_zero_right, integral_zero, mul_one, integral_neg] at h
  exact neg_eq_zero.mp h.symm
/-- The integrated Bochner identity: for `μ = m.tilted (-U)` with `C²` potential `U` and a compactly
supported `C³` function `f`, `∫ Γ₂(f) dμ = ∫ (ℒf)² dμ`. -/
theorem FunctionalInequalities.Analysis.BakryEmery.integral_gammaTwo_eq {U f : E → ℝ} (hU : ContDiff ℝ 2 U) (hf : ContDiff ℝ 3 f)
    (hfc : HasCompactSupport f) :
    ∫ x, gammaTwo U f x ∂(m.tilted (-U)) = ∫ x, weightedLaplacian U f x ^ 2 ∂(m.tilted (-U)) := by
  simp only [gammaTwo_apply]
  rw [integral_sub
    ((integrable_weightedLaplacian_gamma_readable m hU hf hfc).div_const 2)
    (integrable_gamma_weightedLaplacian_readable m hU hf hfc),
    integral_div,
    integral_weightedLaplacian_gamma_eq_zero m hU hf hfc,
    integral_gamma_weightedLaplacian_eq_readable m hU hf hfc]
  ring
/-- Integrated `CD(ρ, ∞)`: if `∇∇U ≥ ρ`, then `ρ ∫ Γ(f) dμ ≤ ∫ (ℒf)² dμ` for every compactly
supported `C³` function `f`. -/
theorem solution {U f : E → ℝ} (hU : ContDiff ℝ 2 U) (hf : ContDiff ℝ 3 f)
    (hfc : HasCompactSupport f) {ρ : ℝ}
    (hH : ∀ x v, ρ * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ U x v v) :
    ρ * ∫ x, FunctionalInequalities.Analysis.BakryEmery.gamma f f x ∂(m.tilted (-U)) ≤ ∫ x, FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian U f x ^ 2 ∂(m.tilted (-U)) := by
  let μ := m.tilted (-U)

  have hgamma : ContDiff ℝ 2 (FunctionalInequalities.Analysis.BakryEmery.gamma f f) := by
    exact FunctionalInequalities.Analysis.BakryEmery.contDiff_gamma (n := 2) hf hf (by norm_num) (by norm_num)

  have hgamma_cont : Continuous (fun x => FunctionalInequalities.Analysis.BakryEmery.gamma f f x) := by
    simpa using hgamma.continuous

  have hgamma_compact : HasCompactSupport (fun x => FunctionalInequalities.Analysis.BakryEmery.gamma f f x) := by
    simpa using FunctionalInequalities.Analysis.BakryEmery.hasCompactSupport_gamma_left f hfc

  have hgamma_integrable : Integrable (fun x => FunctionalInequalities.Analysis.BakryEmery.gamma f f x) μ := by
    dsimp [μ]
    exact hgamma_cont.integrable_of_hasCompactSupport hgamma_compact

  have hscaled_integrable : Integrable (fun x => ρ * FunctionalInequalities.Analysis.BakryEmery.gamma f f x) μ := by
    exact hgamma_integrable.const_mul ρ

  have hgammaTwo_integrable : Integrable (fun x => FunctionalInequalities.Analysis.BakryEmery.gammaTwo U f x) μ := by
    have h₁ :
        Integrable
          ((fun x => FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian U (fun y => FunctionalInequalities.Analysis.BakryEmery.gamma f f y) x / 2) -
            (fun x => FunctionalInequalities.Analysis.BakryEmery.gamma f (FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian U f) x)) μ := by
      exact
        ((FunctionalInequalities.Analysis.BakryEmery.integrable_weightedLaplacian_gamma_readable m hU hf hfc).div_const 2).sub
          (FunctionalInequalities.Analysis.BakryEmery.integrable_gamma_weightedLaplacian_readable m hU hf hfc)
    convert h₁ using 1
    funext x
    rfl

  have hpoint :
      ∀ x, ρ * FunctionalInequalities.Analysis.BakryEmery.gamma f f x ≤ FunctionalInequalities.Analysis.BakryEmery.gammaTwo U f x := by
    intro x
    exact FunctionalInequalities.Analysis.BakryEmery.mul_gamma_le_gammaTwo hU hf hH x

  rw [← integral_const_mul]
  rw [← FunctionalInequalities.Analysis.BakryEmery.integral_gammaTwo_eq m hU hf hfc]
  exact integral_mono hscaled_integrable hgammaTwo_integrable hpoint
