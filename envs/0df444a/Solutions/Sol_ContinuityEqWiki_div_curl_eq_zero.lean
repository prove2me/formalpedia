-- Prove2me | solution 1 for ContinuityEqWiki.div_curl_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Yivy Yu
-- created : 2026-10-27T01:10:08.264189+00:00
-- url     : https://prove2.me/submissions/1e672d70-f4d7-417d-9e53-9769ba011da9

import Mathlib
import Definitions.Def_ContinuityEqWiki_Defs

open ContinuityEqWiki

theorem solution (F : Space → Space) (hF : ContDiff ℝ 2 F) (x : Space) :
    div (curl F) x = 0 := by
  have hcomponent (k : Fin 3) : ContDiff ℝ 2 (fun y => F y k) :=
    (contDiff_apply ℝ ℝ k).comp hF
  have hmixed (k i j : Fin 3) :
      partialDeriv i (fun y => partialDeriv j (fun z => F z k) y) x =
        partialDeriv j (fun y => partialDeriv i (fun z => F z k) y) x := by
    let f : Space → ℝ := fun z => F z k
    have hf : ContDiffAt ℝ 2 f x := (hcomponent k).contDiffAt
    have hdf : DifferentiableAt ℝ (fderiv ℝ f) x :=
      (hf.fderiv_right (by decide)).differentiableAt one_ne_zero
    have happ (v w : Space) :
        fderiv ℝ (fun y => fderiv ℝ f y w) x v =
          fderiv ℝ (fderiv ℝ f) x v w := by
      rw [fderiv_clm_apply hdf (differentiableAt_const w)]
      simp
    unfold partialDeriv
    change fderiv ℝ (fun y => fderiv ℝ f y (Pi.single j 1)) x (Pi.single i 1) =
      fderiv ℝ (fun y => fderiv ℝ f y (Pi.single i 1)) x (Pi.single j 1)
    rw [happ, happ]
    exact hf.isSymmSndFDerivAt (by simp) _ _
  have hpartialDiff (k i : Fin 3) :
      Differentiable ℝ (fun y => partialDeriv i (fun z => F z k) y) := by
    unfold partialDeriv
    have hd : ContDiff ℝ 1 (fderiv ℝ (fun z => F z k)) :=
      (hcomponent k).fderiv_right (by decide)
    exact (hd.clm_apply contDiff_const).differentiable one_ne_zero
  have hpartialSub (i : Fin 3) (f g : Space → ℝ)
      (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
      partialDeriv i (fun y => f y - g y) x =
        partialDeriv i f x - partialDeriv i g x := by
    unfold partialDeriv
    rw [fderiv_fun_sub hf hg]
    rfl
  simp only [div, Fin.sum_univ_three, curl]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.vecHead, Matrix.vecTail]
  simp only [Function.comp_apply, Matrix.cons_val_succ, Matrix.cons_val_zero]
  rw [hpartialSub 0 _ _ ((hpartialDiff 2 1) x) ((hpartialDiff 1 2) x)]
  rw [hpartialSub 1 _ _ ((hpartialDiff 0 2) x) ((hpartialDiff 2 0) x)]
  rw [hpartialSub 2 _ _ ((hpartialDiff 1 0) x) ((hpartialDiff 0 1) x)]
  rw [hmixed 2 0 1, hmixed 1 0 2, hmixed 0 1 2]
  ring
