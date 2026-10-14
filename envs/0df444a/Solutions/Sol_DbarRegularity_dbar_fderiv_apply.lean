-- Prove2me | solution 1 for DbarRegularity.dbar_fderiv_apply
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-13T15:13:33.849912+00:00
-- url     : https://prove2.me/submissions/8dbdf495-2fa6-461f-8b40-cb91f8e8965d

import Definitions.Def_DbarRegularity_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.Complex.Basic



namespace DbarRegularity

open scoped ContDiff

/-- The Cauchy–Riemann operator commutes with a fixed directional derivative on `C²` maps. -/
theorem dbar_fderiv_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {φ : ℂ → E}
    (hφ : ContDiff ℝ 2 φ) (w : ℂ) :
    dbar (fun z => fderiv ℝ φ z w) = fun z => fderiv ℝ (dbar φ) z w := by
  have hfd : ContDiff ℝ 1 (fderiv ℝ φ) := hφ.fderiv_right (by norm_num)
  have hdd : Differentiable ℝ (fderiv ℝ φ) := hfd.differentiable (by norm_num)
  -- directional derivative of `x ↦ Dφ(x) u`
  have hdir : ∀ (u v z : ℂ),
      fderiv ℝ (fun x => fderiv ℝ φ x u) z v = fderiv ℝ (fderiv ℝ φ) z v u := by
    intro u v z
    rw [fderiv_clm_apply (hdd z) (differentiableAt_const u)]
    simp
  funext z
  have hsymm : IsSymmSndFDerivAt ℝ φ z :=
    hφ.contDiffAt.isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField])
  have hA : HasFDerivAt (fun x => fderiv ℝ φ x 1)
      (fderiv ℝ (fun x => fderiv ℝ φ x 1) z) z :=
    ((hdd z).clm_apply (differentiableAt_const _)).hasFDerivAt
  have hB : HasFDerivAt (fun x => fderiv ℝ φ x Complex.I)
      (fderiv ℝ (fun x => fderiv ℝ φ x Complex.I) z) z :=
    ((hdd z).clm_apply (differentiableAt_const _)).hasFDerivAt
  have hdbar : fderiv ℝ (dbar φ) z
      = fderiv ℝ (fun x => fderiv ℝ φ x 1) z
        + Complex.I • fderiv ℝ (fun x => fderiv ℝ φ x Complex.I) z :=
    (hA.add (hB.const_smul Complex.I)).fderiv
  simp only [dbar]
  rw [hdbar, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, hdir, hdir, hdir,
    hdir, hsymm w 1, hsymm w Complex.I]

end DbarRegularity

open DbarRegularity

open scoped ContDiff

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {φ : ℂ → E}
    (hφ : ContDiff ℝ 2 φ) (w : ℂ) :
    dbar (fun z => fderiv ℝ φ z w) = fun z => fderiv ℝ (dbar φ) z w :=
  dbar_fderiv_apply hφ w
