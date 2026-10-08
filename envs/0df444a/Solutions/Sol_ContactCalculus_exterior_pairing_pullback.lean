-- Prove2me | solution 1 for ContactCalculus.exterior_pairing_pullback
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-07T16:36:54.197991+00:00
-- url     : https://prove2.me/submissions/7b38b41f-5e13-4f73-b20a-6f3e8da3852d

import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.Ring

set_option autoImplicit false
open scoped ContDiff

theorem solution {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (α : W → W →L[ℝ] ℝ) (g : V → W) (x u v : V)
    (hα : DifferentiableAt ℝ α (g x)) (hg : ContDiffAt ℝ 2 g x) :
    fderiv ℝ (fun z => (α (g z)).comp (fderiv ℝ g z)) x u v -
      fderiv ℝ (fun z => (α (g z)).comp (fderiv ℝ g z)) x v u =
    fderiv ℝ α (g x) (fderiv ℝ g x u) (fderiv ℝ g x v) -
      fderiv ℝ α (g x) (fderiv ℝ g x v) (fderiv ℝ g x u) := by
  have hgd : DifferentiableAt ℝ g x := hg.differentiableAt (by simp)
  have hgdd : DifferentiableAt ℝ (fderiv ℝ g) x :=
    (hg.fderiv_right (m := 1) (by decide)).differentiableAt (by simp)
  have hd := (hα.hasFDerivAt.comp x hgd.hasFDerivAt).clm_comp hgdd.hasFDerivAt
  have he := hd.fderiv
  simp only [Function.comp_def] at he
  rw [he]
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply]
  rw [(hg.isSymmSndFDerivAt (by simp only [minSmoothness_of_isRCLikeNormedField]; decide)).eq u v]
  ring
