-- Prove2me | solution 1 for GaussMagnetism.curl_add_grad
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T07:47:10.663978+00:00
-- url     : https://prove2.me/submissions/1002c57f-63c7-457c-8322-6bab4cf5bb87

import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Tactic
import Definitions.Def_TongEM_wave_ops
set_option autoImplicit false
open Larmor TongEM

private theorem pd_diff (f : Vec → ℝ) (hf : ContDiff ℝ 2 f) (i : Fin 3) :
    Differentiable ℝ (pd i f) := by
  exact ((hf.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero).clm_apply (differentiable_const _)

private theorem pd_sub (f g : Vec → ℝ) (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (i : Fin 3) (x : Vec) :
    pd i (fun y => f y - g y) x = pd i f x - pd i g x := by
  unfold pd
  rw [fderiv_fun_sub (hf x) (hg x)]
  rfl

private theorem pd_comm (f : Vec → ℝ) (hf : ContDiff ℝ 2 f)
    (i j : Fin 3) (x : Vec) : pd i (pd j f) x = pd j (pd i f) x := by
  have hd := (hf.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  unfold pd
  rw [fderiv_clm_apply (hd x) (differentiableAt_const _), fderiv_clm_apply (hd x) (differentiableAt_const _)]
  simpa using hf.contDiffAt.isSymmSndFDerivAt (by simp) (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)


private theorem partial_eq (F : Vec → Vec) (hF : Differentiable ℝ F) (i j : Fin 3) (x : Vec) :
    Larmor.partialDeriv F i j x = pd i (fun y => F y j) x := by
  have hh := (EuclideanSpace.proj j).hasFDerivAt.comp x (hF x).hasFDerivAt
  change HasFDerivAt (fun y => F y j) _ x at hh
  unfold Larmor.partialDeriv pd
  rw [hh.fderiv]
  rfl

private theorem grad_diff (φ : Vec → ℝ) (hφ : ContDiff ℝ 2 φ) : Differentiable ℝ (grad φ) := by
  apply (differentiable_piLp 2).mpr
  intro i
  fin_cases i
  · exact pd_diff φ hφ 0
  · exact pd_diff φ hφ 1
  · exact pd_diff φ hφ 2

private theorem curlgrad (φ : Vec → ℝ) (hφ : ContDiff ℝ 2 φ) (x : Vec) :
    curl (grad φ) x = 0 := by
  ext i
  fin_cases i
  · change Larmor.partialDeriv (grad φ) 1 2 x - Larmor.partialDeriv (grad φ) 2 1 x = 0
    rw [partial_eq _ (grad_diff φ hφ), partial_eq _ (grad_diff φ hφ)]
    change pd 1 (pd 2 φ) x - pd 2 (pd 1 φ) x = 0
    rw [pd_comm φ hφ 1 2]
    ring
  · change Larmor.partialDeriv (grad φ) 2 0 x - Larmor.partialDeriv (grad φ) 0 2 x = 0
    rw [partial_eq _ (grad_diff φ hφ), partial_eq _ (grad_diff φ hφ)]
    change pd 2 (pd 0 φ) x - pd 0 (pd 2 φ) x = 0
    rw [pd_comm φ hφ 2 0]
    ring
  · change Larmor.partialDeriv (grad φ) 0 1 x - Larmor.partialDeriv (grad φ) 1 0 x = 0
    rw [partial_eq _ (grad_diff φ hφ), partial_eq _ (grad_diff φ hφ)]
    change pd 0 (pd 1 φ) x - pd 1 (pd 0 φ) x = 0
    rw [pd_comm φ hφ 0 1]
    ring

private theorem curl_add (F G : Vec → Vec) (hF : Differentiable ℝ F) (hG : Differentiable ℝ G) (x : Vec) :
    curl (fun y => F y + G y) x = curl F x + curl G x := by
  ext i
  fin_cases i <;> simp [curl, Larmor.partialDeriv, fderiv_fun_add (hF x) (hG x)] <;> ring

theorem solution (A : Vec → Vec) (φ : Vec → ℝ) (hA : ContDiff ℝ 1 A)
    (hφ : ContDiff ℝ 2 φ) (x : Vec) :
    curl (fun y => A y + grad φ y) x = curl A x := by
  rw [curl_add A (grad φ) (hA.differentiable one_ne_zero) (grad_diff φ hφ), curlgrad φ hφ, add_zero]
