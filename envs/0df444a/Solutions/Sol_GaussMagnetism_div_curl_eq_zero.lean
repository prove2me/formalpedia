-- Prove2me | solution 1 for GaussMagnetism.div_curl_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T07:45:31.427655+00:00
-- url     : https://prove2.me/submissions/dc11483e-b0d9-499e-8eb5-c3eafb3083c0

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

private theorem curl_pd (F : Vec → Vec) (hF : Differentiable ℝ F) :
    curl F = fun x => !₂[pd 1 (fun y => F y 2) x - pd 2 (fun y => F y 1) x,
      pd 2 (fun y => F y 0) x - pd 0 (fun y => F y 2) x,
      pd 0 (fun y => F y 1) x - pd 1 (fun y => F y 0) x] := by
  funext x
  ext i
  fin_cases i <;> simp [curl, partial_eq F hF]

private theorem curl_diff (F : Vec → Vec) (hF : ContDiff ℝ 2 F) :
    Differentiable ℝ (curl F) := by
  have hc (i : Fin 3) : ContDiff ℝ 2 (fun y => F y i) := (contDiff_piLp 2).mp hF i
  rw [curl_pd F (hF.differentiable (by norm_num))]
  apply (differentiable_piLp 2).mpr
  intro i
  fin_cases i
  · exact (pd_diff _ (hc 2) 1).sub (pd_diff _ (hc 1) 2)
  · exact (pd_diff _ (hc 0) 2).sub (pd_diff _ (hc 2) 0)
  · exact (pd_diff _ (hc 1) 0).sub (pd_diff _ (hc 0) 1)

theorem solution (A : Vec → Vec) (hA : ContDiff ℝ 2 A) (x : Vec) :
    divg (curl A) x = 0 := by
  have hc (i : Fin 3) : ContDiff ℝ 2 (fun y => A y i) := (contDiff_piLp 2).mp hA i
  unfold divg
  simp_rw [partial_eq _ (curl_diff A hA)]
  rw [curl_pd A (hA.differentiable (by norm_num))]
  change pd 0 (fun y => pd 1 (fun z => A z 2) y - pd 2 (fun z => A z 1) y) x +
    (pd 1 (fun y => pd 2 (fun z => A z 0) y - pd 0 (fun z => A z 2) y) x +
    (pd 2 (fun y => pd 0 (fun z => A z 1) y - pd 1 (fun z => A z 0) y) x + 0)) = 0
  rw [pd_sub _ _ (pd_diff _ (hc 2) 1) (pd_diff _ (hc 1) 2),
    pd_sub _ _ (pd_diff _ (hc 0) 2) (pd_diff _ (hc 2) 0),
    pd_sub _ _ (pd_diff _ (hc 1) 0) (pd_diff _ (hc 0) 1)]
  rw [pd_comm _ (hc 2) 0 1, pd_comm _ (hc 1) 0 2, pd_comm _ (hc 0) 1 2]
  ring
