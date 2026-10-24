-- Prove2me | solution 1 for FunctionalInequalities.Analysis.BakryEmery.iteratedFDeriv_inner_self_apply_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T14:48:04.414118+00:00
-- url     : https://prove2.me/submissions/c1f538bb-4e5e-47a8-ba4b-c5952f2931b1

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
private theorem FunctionalInequalities.Analysis.BakryEmery.eval_deriv {G : E → E} (hG : ContDiff ℝ ∞ G)
    (n : ℕ) (v : Fin n → E) (z : E) :
    HasFDerivAt (fun w => iteratedFDeriv ℝ n G w v)
      ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => E) E v).comp
        (fderiv ℝ (iteratedFDeriv ℝ n G) z)) z := by
  exact
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => E) E v).hasFDerivAt.comp z
      (hG.differentiable_iteratedFDeriv
        (m := n) (by exact_mod_cast ENat.natCast_lt_top n)).differentiableAt.hasFDerivAt
namespace FunctionalInequalities.Analysis.BakryEmery
end FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.BakryEmery in
/-- Leibniz rule with a linear factor: for smooth `G : E → E`,
`∇^{d+1}⟪w, G w⟫(z)(h) = ⟪z, ∇^{d+1}G(z)(h)⟫ + ∑_k ⟪h_k, ∇^d G(z)(h without h_k)⟫`. -/
theorem solution {G : E → E} (hG : ContDiff ℝ ∞ G) (d : ℕ) (z : E)
    (h : Fin (d + 1) → E) :
    iteratedFDeriv ℝ (d + 1) (fun w => ⟪w, G w⟫) z h =
      ⟪z, iteratedFDeriv ℝ (d + 1) G z h⟫ +
        ∑ k : Fin (d + 1), ⟪h k, iteratedFDeriv ℝ d G z (k.removeNth h)⟫ := by
  classical
  induction d generalizing z with
  | zero =>
      rw [iteratedFDeriv_one_apply]
      have hd :=
        (hasFDerivAt_id z).inner ℝ
          (hG.differentiable (by simp)).differentiableAt.hasFDerivAt
      simp only [id_eq] at hd
      rw [hd.fderiv]
      simp [fderivInnerCLM_apply, iteratedFDeriv_one_apply,
        iteratedFDeriv_zero_apply]
  | succ d IH =>
      have hEq :
          (fun w =>
            iteratedFDeriv ℝ (d + 1) (fun y => ⟪y, G y⟫) w (Fin.tail h)) =
          (fun w =>
            ⟪w, iteratedFDeriv ℝ (d + 1) G w (Fin.tail h)⟫ +
              ∑ k : Fin (d + 1),
                ⟪Fin.tail h k,
                  iteratedFDeriv ℝ d G w (k.removeNth (Fin.tail h))⟫) :=
        funext fun w => IH w (Fin.tail h)
      have hmain :=
        (hasFDerivAt_id z).inner ℝ
          (eval_deriv hG (d + 1) (Fin.tail h) z)
      have hsum :=
        HasFDerivAt.fun_sum (u := Finset.univ) (fun k _ =>
          (hasFDerivAt_const (Fin.tail h k) z).inner ℝ
            (eval_deriv hG d (k.removeNth (Fin.tail h)) z))
      have hF : DifferentiableAt ℝ
          (iteratedFDeriv ℝ (d + 1) (fun y => ⟪y, G y⟫)) z :=
        (contDiff_id.inner ℝ hG).differentiable_iteratedFDeriv
          (by exact_mod_cast ENat.natCast_lt_top (d + 1)) z
      simp only [id_eq] at hmain
      rw [hF.iteratedFDeriv_succ_apply_left', hEq,
        (hmain.fun_add hsum).fderiv]
      simp only [add_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply,
        zero_apply, fderivInnerCLM_apply,
        ContinuousMultilinearMap.apply_apply, inner_zero_left, add_zero,
        sum_apply]
      have hcons : Fin.cons (h 0) (Fin.tail h) = h :=
        Fin.cons_self_tail h
      have hremove (k : Fin (d + 1)) :
          Fin.cons (h 0) (k.removeNth (Fin.tail h)) =
            k.succ.removeNth h := by
        rw [← hcons]
        exact
          (Fin.cons_comp_succ_succAbove (h 0) (Fin.tail h) k).symm
      change
        (⟪z, iteratedFDeriv ℝ (d + 1 + 1) G z h⟫ +
          ⟪h 0, iteratedFDeriv ℝ (d + 1) G z (Fin.tail h)⟫) +
          ∑ k : Fin (d + 1),
            ⟪Fin.tail h k,
              fderiv ℝ (iteratedFDeriv ℝ d G) z (h 0)
                (k.removeNth (Fin.tail h))⟫ = _
      conv_rhs => rw [Fin.sum_univ_succ]
      simp only [Fin.removeNth_zero, Fin.tail_def]
      rw [add_assoc]
      congr 1
      congr 1
      apply Finset.sum_congr rfl
      intro k _
      have hh :=
        iteratedFDeriv_succ_apply_left
          (𝕜 := ℝ) (f := G) (x := z)
          (Fin.cons (h 0) (k.removeNth (Fin.tail h)))
      simp only [Fin.cons_zero, Fin.tail_cons] at hh
      rw [hremove k] at hh
      exact congrArg (inner ℝ (h k.succ)) hh.symm
