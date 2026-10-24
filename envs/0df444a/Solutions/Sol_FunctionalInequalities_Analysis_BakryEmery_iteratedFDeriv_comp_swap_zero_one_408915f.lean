-- Prove2me | solution 1 for FunctionalInequalities.Analysis.BakryEmery.iteratedFDeriv_comp_swap_zero_one_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T14:47:04.639058+00:00
-- url     : https://prove2.me/submissions/3e9fdcf7-ab29-4e79-a4f3-eb38638f21bb

import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.InnerProductSpace.Calculus

noncomputable section
open scoped RealInnerProductSpace ContDiff
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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
section Symmetry
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
private theorem FunctionalInequalities.Analysis.BakryEmery.iteratedFDeriv_add_two_apply_left {f : E → F}
    (hf : ContDiff ℝ ∞ f) (n : ℕ) (x : E) (v : Fin (n + 2) → E) :
    iteratedFDeriv ℝ (n + 2) f x v =
      fderiv ℝ (fderiv ℝ (fun y => iteratedFDeriv ℝ n f y (Fin.tail (Fin.tail v))))
        x (v 0) (v 1) := by
  let g : E → F := fun y => iteratedFDeriv ℝ n f y (Fin.tail (Fin.tail v))
  have hT : ContDiff ℝ ∞ (iteratedFDeriv ℝ n f) :=
    hf.iteratedFDeriv_right le_rfl
  have hg : ContDiff ℝ ∞ g :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => E) F
      (Fin.tail (Fin.tail v))).contDiff.comp hT
  have hD : ∀ y, DifferentiableAt ℝ (iteratedFDeriv ℝ n f) y :=
    hT.differentiable (by simp)
  have hD' : DifferentiableAt ℝ (iteratedFDeriv ℝ (n + 1) f) x :=
    (hf.differentiable_iteratedFDeriv (n := ∞) (m := n + 1)
      (ENat.natCast_lt_of_coe_top_le_withTop le_rfl (n + 1))).differentiableAt
  have heq : (fun y => iteratedFDeriv ℝ (n + 1) f y (Fin.tail v)) =
      (fun y => fderiv ℝ g y (v 1)) := by
    funext y
    exact (hD y).iteratedFDeriv_succ_apply_left'
  rw [hD'.iteratedFDeriv_succ_apply_left', heq]
  rw [fderiv_clm_apply ((hg.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x)
    (differentiableAt_const (v 1))]
  simp [g]
namespace FunctionalInequalities.Analysis.BakryEmery
end FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.BakryEmery in
/-- Schwarz's theorem in iterated form: `∇ⁿ⁺²f(x)` is invariant under swapping its first two
indices. -/
theorem solution {f : E → F} (hf : ContDiff ℝ ∞ f) (n : ℕ) (x : E)
    (v : Fin (n + 2) → E) :
    iteratedFDeriv ℝ (n + 2) f x (v ∘ Equiv.swap 0 1) = iteratedFDeriv ℝ (n + 2) f x v := by
  have htail : Fin.tail (Fin.tail (v ∘ Equiv.swap 0 1)) = Fin.tail (Fin.tail v) := by
    ext i
    simp only [Fin.tail, Function.comp_apply]
    rw [Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero i.succ)
      (show i.succ.succ ≠ (1 : Fin (n + 2)) by
        intro h
        have hv := congrArg Fin.val h
        simp only [Fin.val_succ, Fin.val_one] at hv
        omega)]
  rw [iteratedFDeriv_add_two_apply_left hf, iteratedFDeriv_add_two_apply_left hf]
  simp only [Function.comp_apply, Equiv.swap_apply_left, Equiv.swap_apply_right, htail]
  have hT : ContDiff ℝ ∞ (iteratedFDeriv ℝ n f) :=
    hf.iteratedFDeriv_right le_rfl
  have hg : ContDiff ℝ ∞ (fun y => iteratedFDeriv ℝ n f y (Fin.tail (Fin.tail v))) :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => E) F
      (Fin.tail (Fin.tail v))).contDiff.comp hT
  exact (hg.contDiffAt.isSymmSndFDerivAt (by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact le_of_lt (ENat.natCast_lt_of_coe_top_le_withTop le_rfl 2)))
    (v 1) (v 0)
