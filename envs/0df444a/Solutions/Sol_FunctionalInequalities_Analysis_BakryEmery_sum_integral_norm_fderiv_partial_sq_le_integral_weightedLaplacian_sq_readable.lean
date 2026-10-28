-- Prove2me | solution 1 for FunctionalInequalities.Analysis.BakryEmery.sum_integral_norm_fderiv_partial_sq_le_integral_weightedLaplacian_sq_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:26:55.315526+00:00
-- url     : https://prove2.me/submissions/6ba066a4-b569-448a-88d8-0d145b0d890f

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Gamma
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Bochner_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Curvature
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HminusOne
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
section Hessian
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- The bilinear second Fréchet derivative of a `C²` real-valued function is symmetric. -/
theorem FunctionalInequalities.Analysis.BakryEmery.bilinearIteratedFDerivTwo_symm {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (x v w : E) :
    bilinearIteratedFDerivTwo ℝ f x v w =
      bilinearIteratedFDerivTwo ℝ f x w v := by
  rw [bilinearIteratedFDerivTwo_eq_iteratedFDeriv,
    bilinearIteratedFDerivTwo_eq_iteratedFDeriv]
  exact (hf.contDiffAt.isSymmSndFDerivAt (by simp)).iteratedFDeriv_cons
end Hessian
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

section
noncomputable section
open MeasureTheory InnerProductSpace
open scoped ContDiff RealInnerProductSpace
section
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
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
end
end
end

noncomputable section
open MeasureTheory
open scoped ContDiff
section LT9CBochnerHessianBound
open InnerProductSpace
variable {n : ℕ}
private theorem FunctionalInequalities.Analysis.BakryEmery.partial_integrable
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsFiniteMeasureOnCompacts μ]
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : ContDiff ℝ ∞ g)
    (hgc : HasCompactSupport g) (i : Fin n) :
    Integrable
      (fun x =>
        ‖fderiv ℝ (fun y => fderiv ℝ g y (EuclideanSpace.single i 1)) x‖ ^ 2)
      μ := by
  let e : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single i 1
  have hg3 : ContDiff ℝ 3 g :=
    hg.of_le (WithTop.coe_le_coe.mpr le_top)
  have hq : HasCompactSupport (fun y => fderiv ℝ g y e) := by
    have h :=
      (hgc.fderiv (𝕜 := ℝ)).comp_left
        (g := fun A : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ => A e) (by simp)
    simpa [e, Function.comp_def] using h
  have hq' : HasCompactSupport (fderiv ℝ (fun y => fderiv ℝ g y e)) :=
    hq.fderiv (𝕜 := ℝ)
  have hqcont :
      Continuous (fderiv ℝ (fun y => fderiv ℝ g y e)) := by
    exact
      (contDiff_fderiv_apply hg3 (m := 2) (by norm_num) e).continuous_fderiv
        (by norm_num)
  have hcont :
      Continuous
        (fun x => ‖fderiv ℝ (fun y => fderiv ℝ g y e) x‖ ^ 2) :=
    (hqcont.norm).pow 2
  have hn :
      HasCompactSupport
        (fun x => ‖fderiv ℝ (fun y => fderiv ℝ g y e) x‖ ^ 2) := by
    simpa [Function.comp_def] using
      (hq'.norm.comp_left (g := fun r : ℝ => r ^ 2) (by simp))
  have hi :
      Integrable
        (fun x => ‖fderiv ℝ (fun y => fderiv ℝ g y e) x‖ ^ 2) μ :=
    hcont.integrable_of_hasCompactSupport hn
  simpa [e] using hi
section HaarReference
variable (m : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)))
private theorem FunctionalInequalities.Analysis.BakryEmery.gammaTwo_integrable [m.IsAddHaarMeasure]
    {W g : EuclideanSpace ℝ (Fin n) → ℝ} (hW : ContDiff ℝ 2 W)
    (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    Integrable (gammaTwo W g) (m.tilted (-W)) := by
  let ν := m.tilted (-W)
  have hg3 : ContDiff ℝ 3 g :=
    hg.of_le (WithTop.coe_le_coe.mpr le_top)
  have h₁ :
      Integrable
        ((fun x =>
            weightedLaplacian W (fun y => gamma g g y) x / 2) -
          (fun x => gamma g (weightedLaplacian W g) x)) ν := by
    dsimp [ν]
    exact
      ((integrable_weightedLaplacian_gamma_readable m hW hg3 hgc).div_const 2).sub
        (integrable_gamma_weightedLaplacian_readable m hW hg3 hgc)
  have hrepr :
      (fun x => gammaTwo W g x) =
        (fun x =>
          weightedLaplacian W (fun y => gamma g g y) x / 2 -
            gamma g (weightedLaplacian W g) x) := by
    funext x
    exact gammaTwo_apply W g x
  change Integrable (fun x => gammaTwo W g x) ν
  rw [hrepr]
  exact h₁
/-- **Bochner bound for the coordinate Hessian under a convex `C²` potential** (Letwin
arXiv:2607.24164v1, Proposition 2.8 via Barthe–Klartag; weak Letwin route): for
`ν = e^{-W} dm` with `W` convex and `C²`, and `g ∈ C_c^∞`,
`∑ᵢ ∫ ‖∇(∂ᵢ g)‖² dν ≤ ∫ (ℒg)² dν` with `ℒg = Δg − ⟪∇W, ∇g⟫` and `∂ᵢ g = Dg(eᵢ)` in the
standard coordinates of `EuclideanSpace ℝ (Fin n)`. -/
theorem solution [m.IsAddHaarMeasure]
    {W : EuclideanSpace ℝ (Fin n) → ℝ} (hW : ContDiff ℝ 2 W) (hWc : ConvexOn ℝ Set.univ W)
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    ∑ i, ∫ x, ‖fderiv ℝ (fun y => fderiv ℝ g y (EuclideanSpace.single i 1)) x‖ ^ 2
        ∂(m.tilted (-W)) ≤
      ∫ x, FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian W g x ^ 2 ∂(m.tilted (-W)) := by
  let ν := m.tilted (-W)
  let e : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) :=
    EuclideanSpace.basisFun (Fin n) ℝ
  let b : OrthonormalBasis (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))) ℝ
      (EuclideanSpace ℝ (Fin n)) :=
    stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin n))
  have hg3 : ContDiff ℝ 3 g :=
    hg.of_le (WithTop.coe_le_coe.mpr le_top)
  have hg2 : ContDiff ℝ 2 g :=
    hg.of_le (WithTop.coe_le_coe.mpr le_top)
  have hpoint :
      ∀ x,
        FunctionalInequalities.Analysis.BakryEmery.hessianSqStdBasis g x =
          ∑ i, ‖fderiv ℝ
            (fun y => fderiv ℝ g y (EuclideanSpace.single i 1)) x‖ ^ 2 := by
    intro x
    have hB (v w : EuclideanSpace ℝ (Fin n)) :
        inner ℝ (gradient (fun y => fderiv ℝ g y v) x) w =
          bilinearIteratedFDerivTwo ℝ g x w v := by
      calc
        inner ℝ (gradient (fun y => fderiv ℝ g y v) x) w =
            fderiv ℝ (fun y => fderiv ℝ g y v) x w :=
          inner_gradient_left
        _ = bilinearIteratedFDerivTwo ℝ g x w v :=
          (FunctionalInequalities.Analysis.BakryEmery.bilinearIteratedFDerivTwo_eq_fderiv_apply hg2 x w v).symm
    have hnorm (v : EuclideanSpace ℝ (Fin n)) :
        ‖fderiv ℝ (fun y => fderiv ℝ g y v) x‖ ^ 2 =
          ‖gradient (fun y => fderiv ℝ g y v) x‖ ^ 2 := by
      have heq :
          fderiv ℝ (fun y => fderiv ℝ g y v) x =
            (innerSL ℝ) (gradient (fun y => fderiv ℝ g y v) x) := by
        ext w
        calc
          fderiv ℝ (fun y => fderiv ℝ g y v) x w =
              inner ℝ (gradient (fun y => fderiv ℝ g y v) x) w :=
            (inner_gradient_left).symm
          _ = ((innerSL ℝ) (gradient (fun y => fderiv ℝ g y v) x)) w := by
            rw [innerSL_apply_apply]
      rw [heq, innerSL_apply_norm]
    have hmain :
        (∑ i, ‖gradient
            (fun y => fderiv ℝ g y (e i)) x‖ ^ 2) =
          ∑ j, ‖gradient
            (fun y => fderiv ℝ g y (b j)) x‖ ^ 2 := by
      calc
        (∑ i, ‖gradient
            (fun y => fderiv ℝ g y (e i)) x‖ ^ 2) =
            ∑ i, ∑ j, inner ℝ
              (gradient (fun y => fderiv ℝ g y (e i)) x) (b j) ^ 2 := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [b.sum_sq_inner_left]
        _ = ∑ i, ∑ j,
            (bilinearIteratedFDerivTwo ℝ g x (b j) (e i)) ^ 2 := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          rw [hB]
        _ = ∑ j, ∑ i,
            (bilinearIteratedFDerivTwo ℝ g x (b j) (e i)) ^ 2 := by
          rw [Finset.sum_comm]
        _ = ∑ j, ∑ i,
            (bilinearIteratedFDerivTwo ℝ g x (e i) (b j)) ^ 2 := by
          apply Finset.sum_congr rfl
          intro j hj
          apply Finset.sum_congr rfl
          intro i hi
          exact congrArg (fun z : ℝ => z ^ 2)
            (FunctionalInequalities.Analysis.BakryEmery.bilinearIteratedFDerivTwo_symm hg2 x (b j) (e i))
        _ = ∑ j, ∑ i, inner ℝ
            (gradient (fun y => fderiv ℝ g y (b j)) x) (e i) ^ 2 := by
          apply Finset.sum_congr rfl
          intro j hj
          apply Finset.sum_congr rfl
          intro i hi
          rw [hB]
        _ = ∑ j, ‖gradient
            (fun y => fderiv ℝ g y (b j)) x‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [e.sum_sq_inner_left]
    have hb :
        FunctionalInequalities.Analysis.BakryEmery.hessianSqStdBasis g x =
          ∑ j, ‖gradient (fun y => fderiv ℝ g y (b j)) x‖ ^ 2 := by
      have hb' :
          (∑ i, ∑ j,
              (bilinearIteratedFDerivTwo ℝ g x (b i) (b j)) ^ 2) =
            ∑ j, ‖gradient
              (fun y => fderiv ℝ g y (b j)) x‖ ^ 2 := by
        calc
          (∑ i, ∑ j,
              (bilinearIteratedFDerivTwo ℝ g x (b i) (b j)) ^ 2) =
              ∑ j, ∑ i,
                (bilinearIteratedFDerivTwo ℝ g x (b i) (b j)) ^ 2 := by
            rw [Finset.sum_comm]
          _ = ∑ j, ∑ i, inner ℝ
              (gradient (fun y => fderiv ℝ g y (b j)) x) (b i) ^ 2 := by
            apply Finset.sum_congr rfl
            intro j hj
            apply Finset.sum_congr rfl
            intro i hi
            rw [hB]
          _ = ∑ j, ‖gradient
              (fun y => fderiv ℝ g y (b j)) x‖ ^ 2 := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [b.sum_sq_inner_left]
      simpa [FunctionalInequalities.Analysis.BakryEmery.hessianSqStdBasis, b] using hb'
    have hcoord :
        (∑ i, ‖fderiv ℝ
            (fun y => fderiv ℝ g y (EuclideanSpace.single i 1)) x‖ ^ 2) =
          ∑ i, ‖gradient
            (fun y => fderiv ℝ g y (e i)) x‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [EuclideanSpace.basisFun_apply]
      exact hnorm _
    calc
      FunctionalInequalities.Analysis.BakryEmery.hessianSqStdBasis g x =
          ∑ j, ‖gradient (fun y => fderiv ℝ g y (b j)) x‖ ^ 2 := hb
      _ = ∑ i, ‖gradient
          (fun y => fderiv ℝ g y (e i)) x‖ ^ 2 := hmain.symm
      _ = ∑ i, ‖fderiv ℝ
          (fun y => fderiv ℝ g y (EuclideanSpace.single i 1)) x‖ ^ 2 :=
        hcoord.symm
  have hsum :
      (∫ x, ∑ i, ‖fderiv ℝ
          (fun y => fderiv ℝ g y (EuclideanSpace.single i 1)) x‖ ^ 2 ∂ν) =
        ∑ i, ∫ x, ‖fderiv ℝ
          (fun y => fderiv ℝ g y (EuclideanSpace.single i 1)) x‖ ^ 2 ∂ν := by
    rw [integral_finsetSum]
    intro i hi
    exact FunctionalInequalities.Analysis.BakryEmery.partial_integrable ν hg hgc i
  have hgamma : Integrable (FunctionalInequalities.Analysis.BakryEmery.gammaTwo W g) ν := by
    simpa [ν] using FunctionalInequalities.Analysis.BakryEmery.gammaTwo_integrable m hW hg hgc
  have hzero : 0 ≤ᵐ[ν] fun x => FunctionalInequalities.Analysis.BakryEmery.hessianSqStdBasis g x :=
    Filter.Eventually.of_forall (fun x => FunctionalInequalities.Analysis.BakryEmery.hessianSqStdBasis_nonneg g x)
  have hle :
      ∀ x, FunctionalInequalities.Analysis.BakryEmery.hessianSqStdBasis g x ≤ FunctionalInequalities.Analysis.BakryEmery.gammaTwo W g x := by
    intro x
    rw [FunctionalInequalities.Analysis.BakryEmery.gammaTwo_eq_hessianSqStdBasis_add_readable hW hg3 x]
    exact le_add_of_nonneg_right
      (FunctionalInequalities.Analysis.BakryEmery.bilinearIteratedFDerivTwo_nonneg_of_convexOn hW hWc x (gradient g x))
  have hmono :
      (∫ x, FunctionalInequalities.Analysis.BakryEmery.hessianSqStdBasis g x ∂ν) ≤
        ∫ x, FunctionalInequalities.Analysis.BakryEmery.gammaTwo W g x ∂ν :=
    integral_mono_of_nonneg hzero hgamma
      (Filter.Eventually.of_forall hle)
  calc
    ∑ i, ∫ x, ‖fderiv ℝ
        (fun y => fderiv ℝ g y (EuclideanSpace.single i 1)) x‖ ^ 2 ∂ν =
        ∫ x, ∑ i, ‖fderiv ℝ
          (fun y => fderiv ℝ g y (EuclideanSpace.single i 1)) x‖ ^ 2 ∂ν :=
      hsum.symm
    _ = ∫ x, FunctionalInequalities.Analysis.BakryEmery.hessianSqStdBasis g x ∂ν := by
      congr 1
      funext x
      exact (hpoint x).symm
    _ ≤ ∫ x, FunctionalInequalities.Analysis.BakryEmery.gammaTwo W g x ∂ν := hmono
    _ = ∫ x, FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian W g x ^ 2 ∂ν := by
      simpa [ν] using
        (FunctionalInequalities.Analysis.BakryEmery.integral_gammaTwo_eq m hW hg3 hgc)
