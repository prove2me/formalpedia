-- Prove2me | solution 1 for FunctionalInequalities.Analysis.directional_bilinear_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T14:47:07.600678+00:00
-- url     : https://prove2.me/submissions/96055da5-f483-4934-b056-6facf7d0ee67

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_IteratedDerivative_Bilinear
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_IteratedDerivative_Symmetry
import Mathlib.Algebra.BigOperators.Group.Finset.Pi
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Data.List.FinRange

section
noncomputable section
open scoped ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
theorem FunctionalInequalities.Analysis.directional_contDiff {f : E → F} (hf : ContDiff ℝ ∞ f) (hs : List E) :
    ContDiff ℝ ∞ (directional hs f) := by
  induction hs with
  | nil => exact hf
  | cons h hs IH =>
    exact (ContinuousLinearMap.apply ℝ F h).contDiff.comp (IH.fderiv_right (by simp))
end
end
end
end

noncomputable section
open scoped ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
variable {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
omit [NormedSpace ℝ H] in
private theorem FunctionalInequalities.Analysis.sum_masks_succ {m : ℕ} (Φ : (Fin (m+1) → Bool) → H) :
    (∑ q, Φ q) = (∑ q : Fin m → Bool, Φ (Fin.cons false q)) +
      ∑ q : Fin m → Bool, Φ (Fin.cons true q) := by
  rw [← (Fin.consEquiv (fun _ : Fin (m+1) => Bool)).sum_comp]
  rw [Fintype.sum_prod_type]
  have hb : (Finset.univ : Finset Bool) = {false, true} := by
    ext q
    cases q <;> simp
  rw [hb]
  simp [Fin.consEquiv]
private theorem FunctionalInequalities.Analysis.directional_bilinear_one (B : F →L[ℝ] G →L[ℝ] H)
    {f : E → F} {g : E → G} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (v x : E) :
    fderiv ℝ (fun y => B (f y) (g y)) x v =
      B (f x) (fderiv ℝ g x v) + B (fderiv ℝ f x v) (g x) := by
  rw [B.fderiv_of_bilinear (hf.differentiable (by simp) x) (hg.differentiable (by simp) x)]
  rfl
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
/-- Exact raw higher Leibniz rule for an arbitrary continuous bilinear map.
Each Boolean indicator chooses the derivatives falling on the first factor. -/
theorem solution (B : F →L[ℝ] G →L[ℝ] H)
    {f : E → F} {g : E → G} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (m : ℕ) (h : Fin m → E) (x : E) :
    FunctionalInequalities.Analysis.directional (List.ofFn h) (fun y => B (f y) (g y)) x =
      ∑ q : Fin m → Bool,
        B (FunctionalInequalities.Analysis.directional (FunctionalInequalities.Analysis.selected h q) f x)
          (FunctionalInequalities.Analysis.directional (FunctionalInequalities.Analysis.selected h (fun i => !(q i))) g x) := by
  induction m generalizing x with
  | zero => simp [FunctionalInequalities.Analysis.directional, FunctionalInequalities.Analysis.selected]
  | succ m IH =>
    rw [List.ofFn_succ]
    change fderiv ℝ (FunctionalInequalities.Analysis.directional (List.ofFn (Fin.tail h)) (fun y => B (f y) (g y))) x (h 0) = _
    have he : FunctionalInequalities.Analysis.directional (List.ofFn (Fin.tail h)) (fun y => B (f y) (g y)) =
        fun y => ∑ q : Fin m → Bool,
          B (FunctionalInequalities.Analysis.directional (FunctionalInequalities.Analysis.selected (Fin.tail h) q) f y)
            (FunctionalInequalities.Analysis.directional (FunctionalInequalities.Analysis.selected (Fin.tail h) (fun i => !(q i))) g y) :=
      funext (fun y => IH (Fin.tail h) y)
    rw [he]
    have hCD (q : Fin m → Bool) : ContDiff ℝ ∞ (fun y =>
        B (FunctionalInequalities.Analysis.directional (FunctionalInequalities.Analysis.selected (Fin.tail h) q) f y)
          (FunctionalInequalities.Analysis.directional (FunctionalInequalities.Analysis.selected (Fin.tail h) (fun i => !(q i))) g y)) :=
      B.isBoundedBilinearMap.contDiff.comp
        ((FunctionalInequalities.Analysis.directional_contDiff hf _).prodMk (FunctionalInequalities.Analysis.directional_contDiff hg _))
    rw [fderiv_fun_sum (fun q _ => (hCD q).differentiable (by simp) x)]
    simp only [sum_apply]
    rw [sum_masks_succ]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q _hq
    rw [directional_bilinear_one B (FunctionalInequalities.Analysis.directional_contDiff hf _) (FunctionalInequalities.Analysis.directional_contDiff hg _)]
    simp only [FunctionalInequalities.Analysis.selected, Fin.cons_zero, Bool.false_eq_true, ↓reduceIte, Fin.tail_cons,
      Bool.not_false, Bool.not_true, FunctionalInequalities.Analysis.directional]
    rfl
