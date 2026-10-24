-- Prove2me | solution 1 for FunctionalInequalities.Analysis.BakryEmery.integral_gamma_weightedLaplacian_eq_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T14:46:31.001184+00:00
-- url     : https://prove2.me/submissions/618a910b-a05a-495b-90a0-6ff12dd17848

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Bochner_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Gamma
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.Tilted

section
noncomputable section
open InnerProductSpace
open scoped ContDiff RealInnerProductSpace
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
section StdBasis
variable [FiniteDimensional ℝ E]
variable [CompleteSpace E]
omit [CompleteSpace E] in
/-- The Laplacian as the trace of the iterated directional derivatives, at a point where the
derivative is differentiable. -/
theorem FunctionalInequalities.Analysis.BakryEmery.laplacian_eq_sum_fderiv_apply_fderiv_apply {g : E → ℝ} {x : E}
    (hg : DifferentiableAt ℝ (fderiv ℝ g) x) :
    Laplacian.laplacian g x =
      ∑ i, fderiv ℝ (fun y => fderiv ℝ g y (stdOrthonormalBasis ℝ E i)) x
        (stdOrthonormalBasis ℝ E i) := by
  rw [laplacian_eq_sum_fderiv_fderiv]
  exact Finset.sum_congr rfl fun i _ => (fderiv_fderiv_apply hg _ _).symm
omit [CompleteSpace E] in
/-- The Laplacian of a `C²` function as a function: the trace of the iterated directional
derivatives in the standard orthonormal basis. -/
theorem FunctionalInequalities.Analysis.BakryEmery.laplacian_eq_fun_sum {g : E → ℝ} (hg : ContDiff ℝ 2 g) :
    Laplacian.laplacian g = fun x =>
      ∑ i, fderiv ℝ (fun y => fderiv ℝ g y (stdOrthonormalBasis ℝ E i)) x
        (stdOrthonormalBasis ℝ E i) :=
  funext fun x => laplacian_eq_sum_fderiv_apply_fderiv_apply
    ((hg.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero x)
omit [CompleteSpace E] in
/-- The Laplacian of a `C^n` function is `C^m` when `m + 2 ≤ n`. -/
theorem FunctionalInequalities.Analysis.BakryEmery.contDiff_laplacian {g : E → ℝ} {n m : WithTop ℕ∞} (hg : ContDiff ℝ n g) (hmn : m + 2 ≤ n) :
    ContDiff ℝ m (Laplacian.laplacian g) := by
  have h2 : (2 : WithTop ℕ∞) ≤ n := le_trans (by simp) hmn
  rw [laplacian_eq_fun_sum (hg.of_le h2)]
  refine ContDiff.sum fun i _ => ?_
  refine contDiff_fderiv_apply (contDiff_fderiv_apply hg ?_ _) le_rfl _
  calc m + 1 + 1 = m + 2 := by rw [add_assoc]; norm_num
    _ ≤ n := hmn
end StdBasis
end DifferentialTools
end
end
end
end
end

section
noncomputable section
open MeasureTheory InnerProductSpace
open scoped ContDiff RealInnerProductSpace
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
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
/-- Regularity of the weighted Laplacian: a `C^{n+1}` potential and `C^{n+2}` data give a `C^n`
weighted Laplacian. -/
theorem FunctionalInequalities.Analysis.BakryEmery.contDiff_weightedLaplacian {n p q : WithTop ℕ∞} {U f : E → ℝ} (hU : ContDiff ℝ p U)
    (hf : ContDiff ℝ q f) (hp : n + 1 ≤ p) (hq : n + 2 ≤ q) :
    ContDiff ℝ n (weightedLaplacian U f) := by
  have hnq : n + 1 ≤ q :=
    le_trans (by gcongr; norm_num : n + (1 : WithTop ℕ∞) ≤ n + 2) hq
  exact ContDiff.sub (contDiff_laplacian hf hq)
    (ContDiff.inner ℝ (contDiff_gradient hU hp) (contDiff_gradient hf hnq))
end
end
end
end
end

section
noncomputable section
open InnerProductSpace
open scoped ContDiff RealInnerProductSpace
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
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
section Gamma
variable [CompleteSpace E]
theorem FunctionalInequalities.Analysis.BakryEmery.gamma_apply (f g : E → ℝ) (x : E) : gamma f g x = ⟪gradient f x, gradient g x⟫ := rfl
variable [FiniteDimensional ℝ E]
end Gamma
end
end
end
end
end

noncomputable section
open MeasureTheory InnerProductSpace
open scoped ContDiff RealInnerProductSpace
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
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E] (m : Measure E) [m.IsAddHaarMeasure]
namespace FunctionalInequalities.Analysis.BakryEmery
end FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.BakryEmery in
/-- Integration by parts: `∫ Γ(f, ℒf) dμ = -∫ (ℒf)² dμ` for `μ = m.tilted (-U)`. -/
theorem solution {U f : E → ℝ} (hU : ContDiff ℝ 2 U)
    (hf : ContDiff ℝ 3 f) (hfc : HasCompactSupport f) :
    ∫ x, FunctionalInequalities.Analysis.BakryEmery.gamma f (FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian U f) x ∂(m.tilted (-U)) =
      -∫ x, FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian U f x ^ 2 ∂(m.tilted (-U)) := by
  have hL : ContDiff ℝ 1 (FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian U f) := by
    exact FunctionalInequalities.Analysis.BakryEmery.contDiff_weightedLaplacian (n := 1) hU hf
      (by norm_num) (by norm_num)
  have h :=
    FunctionalInequalities.Analysis.BakryEmery.integral_inner_gradient_tilted m
      (U := U) (f := f) (g := FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian U f)
      (hU.of_le (by norm_num))
      (hf.of_le (by norm_num))
      hfc hL
  calc
    ∫ x, FunctionalInequalities.Analysis.BakryEmery.gamma f (FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian U f) x ∂(m.tilted (-U)) =
        ∫ x, ⟪gradient f x, gradient (FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian U f) x⟫
          ∂(m.tilted (-U)) := by
            simp only [FunctionalInequalities.Analysis.BakryEmery.gamma_apply]
    _ = ∫ x, -FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian U f x * FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian U f x
          ∂(m.tilted (-U)) := h
    _ = ∫ x, -(FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian U f x ^ 2) ∂(m.tilted (-U)) := by
          congr 1
          funext x
          ring
    _ = -∫ x, FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian U f x ^ 2 ∂(m.tilted (-U)) := by
          rw [integral_neg]
