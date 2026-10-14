-- Prove2me | solution 1 for ContDiff.iterate_directional_mul
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-12T17:55:24.130917+00:00
-- url     : https://prove2.me/submissions/03264345-77d0-44fb-aef1-8194e357d6c7

import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Pi.Interval
import Mathlib.Data.Fin.Tuple.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring

open scoped ContDiff
set_option autoImplicit false

noncomputable def directional {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : E) (f : E → ℝ) : E → ℝ := fun x => fderiv ℝ f x a

theorem directional_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : E) {f : E → ℝ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (directional a f) := by
  exact (hf.contDiff_fderiv_apply (m := ∞) (by simp)).comp
    (contDiff_id.prodMk contDiff_const)

theorem directional_iter_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : E) (k : ℕ) {f : E → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ ((directional a)^[k] f) := by
  induction k with
  | zero => exact hf
  | succ k ih => simpa only [Function.iterate_succ_apply'] using directional_smooth a ih

theorem directional_sum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} (a : E) (s : Finset ι) (f : ι → E → ℝ)
    (hf : ∀ j ∈ s, ContDiff ℝ ∞ (f j)) :
    directional a (fun x => ∑ j ∈ s, f j x) = fun x => ∑ j ∈ s, directional a (f j) x := by
  funext x
  simp only [directional, fderiv_fun_sum (fun j hj =>
    ((hf j hj).differentiable (by simp)).differentiableAt), ContinuousLinearMap.sum_apply]

theorem directional_const_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : E) (c : ℝ) {f : E → ℝ} (hf : ContDiff ℝ ∞ f) :
    directional a (fun x => c * f x) = fun x => c * directional a f x := by
  funext x
  simp only [directional, fderiv_const_mul ((hf.differentiable (by simp)).differentiableAt),
    ContinuousLinearMap.smul_apply, smul_eq_mul]

theorem directional_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : E) {f g : E → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    directional a (fun x => f x * g x) =
      fun x => directional a f x * g x + f x * directional a g x := by
  funext x
  simp only [directional, fderiv_fun_mul ((hf.differentiable (by simp)).differentiableAt)
    ((hg.differentiable (by simp)).differentiableAt), ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem directional_iter_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : E) (k : ℕ) {f g : E → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    (directional a)^[k] (fun x => f x * g x) = fun x =>
      ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) *
        (((directional a)^[k-j] f) x * ((directional a)^[j] g) x) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, directional_sum]
    · funext x
      rw [Finset.sum_choose_succ_mul (fun j l =>
        ((directional a)^[l] f) x * ((directional a)^[j] g) x) k]
      simp only [directional_const_mul a _ ((directional_iter_smooth a _ hf).mul
        (directional_iter_smooth a _ hg)),
        directional_mul a (directional_iter_smooth a _ hf) (directional_iter_smooth a _ hg)]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      have h : j ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      rw [show k + 1 - j = (k-j) + 1 by omega]
      simp only [Function.iterate_succ_apply', directional]
      ring
    · intro j hj
      exact contDiff_const.mul ((directional_iter_smooth a _ hf).mul
        (directional_iter_smooth a _ hg))

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : E) (k : ℕ) (f g : E → ℝ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    (fun u y => fderiv ℝ u y a)^[k] (fun x => f x * g x) = fun x =>
      ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) *
        (((fun u y => fderiv ℝ u y a)^[k-j] f) x *
         ((fun u y => fderiv ℝ u y a)^[j] g) x) := by
  exact directional_iter_mul a k hf hg
