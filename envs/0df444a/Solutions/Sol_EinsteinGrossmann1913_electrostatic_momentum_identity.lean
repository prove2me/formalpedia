-- Prove2me | solution 1 for EinsteinGrossmann1913.electrostatic_momentum_identity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T07:31:27.219346+00:00
-- url     : https://prove2.me/submissions/f3655cd5-33c1-4b91-8a83-da09d7286092

import Mathlib
import Definitions.Def_EinsteinGrossmann1913_Defs
open EinsteinGrossmann1913

namespace EGAux

lemma pd_pd_eq {n : ℕ} (φ : (Fin n → ℝ) → ℝ) (hφ : ContDiff ℝ 2 φ) (i j : Fin n) (x : Fin n → ℝ) :
    pd i (pd j φ) x = fderiv ℝ (fderiv ℝ φ) x (Pi.single i 1) (Pi.single j 1) := by
  unfold pd
  have hd : DifferentiableAt ℝ (fderiv ℝ φ) x :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x
  rw [fderiv_clm_apply hd (differentiableAt_const _)]
  simp

lemma pd_comm {n : ℕ} (φ : (Fin n → ℝ) → ℝ) (hφ : ContDiff ℝ 2 φ) (i j : Fin n) (x : Fin n → ℝ) :
    pd i (pd j φ) x = pd j (pd i φ) x := by
  rw [pd_pd_eq φ hφ, pd_pd_eq φ hφ]
  exact (hφ.contDiffAt.isSymmSndFDerivAt (by simp)) _ _

lemma pd_diff {n : ℕ} (φ : (Fin n → ℝ) → ℝ) (hφ : ContDiff ℝ 2 φ) (j : Fin n) :
    Differentiable ℝ (pd j φ) := by
  unfold pd
  have hd : Differentiable ℝ (fderiv ℝ φ) :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  exact fun x => (hd x).clm_apply (differentiableAt_const _)

lemma pd_mul {n : ℕ} (f g : (Fin n → ℝ) → ℝ) (i : Fin n) (x : Fin n → ℝ)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    pd i (fun y => f y * g y) x = pd i f x * g x + f x * pd i g x := by
  unfold pd
  have h : HasFDerivAt (fun y => f y * g y) _ x := hf.hasFDerivAt.mul hg.hasFDerivAt
  rw [h.fderiv]
  simp; ring

end EGAux

open EGAux in
theorem solution (φ : (Fin 3 → ℝ) → ℝ) (hφ : ContDiff ℝ 2 φ)
    (ν : Fin 3) (x : Fin 3 → ℝ) :
    (∑ μ : Fin 3, pd μ (fun y => pd ν φ y * pd μ φ y) x)
      - pd ν (fun y => (1 / 2) * ∑ μ : Fin 3, (pd μ φ y) ^ 2) x
      = pd ν φ x * ∑ μ : Fin 3, pd μ (pd μ φ) x := by
  have hd := pd_diff φ hφ
  have e1 : ∀ μ, pd μ (fun y => pd ν φ y * pd μ φ y) x
      = pd ν (pd μ φ) x * pd μ φ x + pd ν φ x * pd μ (pd μ φ) x := by
    intro μ
    rw [pd_mul _ _ μ x (hd ν x) (hd μ x), pd_comm φ hφ μ ν]
  have e2 : pd ν (fun y => (1 / 2) * ∑ μ : Fin 3, (pd μ φ y) ^ 2) x
      = ∑ μ : Fin 3, pd μ φ x * pd ν (pd μ φ) x := by
    have hD : ∀ μ, HasFDerivAt (pd μ φ) (fderiv ℝ (pd μ φ) x) x := fun μ => (hd μ x).hasFDerivAt
    have h := (HasFDerivAt.fun_sum (u := Finset.univ) (fun μ _ => (hD μ).pow 2)).const_mul (1/2 : ℝ)
    unfold pd at h ⊢
    rw [h.fderiv]
    simp [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun μ _ => ?_)
    ring
  rw [Finset.sum_congr rfl (fun μ _ => e1 μ), e2, Finset.sum_add_distrib, Finset.mul_sum]
  have : ∑ μ : Fin 3, pd ν (pd μ φ) x * pd μ φ x = ∑ μ : Fin 3, pd μ φ x * pd ν (pd μ φ) x :=
    Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  rw [this]; ring
