-- Prove2me | solution 1 for BianchiIX.hasDerivAt_observable_variation
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T23:28:01.71695+00:00
-- url     : https://prove2.me/submissions/174b4725-c23a-45d4-b7ea-b6ea8be0502c

import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic.Module


namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX
open Filter
open scoped Topology
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]


/-- The variation of an observable differentiates its directional derivative along the field. -/
theorem solution
    {p : E → F} {f : E → E} {alpha v : ℝ → E} {t : ℝ}
    (hp : ContDiffAt ℝ 2 p (alpha t)) (hf : DifferentiableAt ℝ f (alpha t))
    (ha : HasDerivAt alpha (f (alpha t)) t)
    (hv : HasDerivAt v (fderiv ℝ f (alpha t) (v t)) t) :
    HasDerivAt (fun s => fderiv ℝ p (alpha s) (v s))
      (fderiv ℝ (fun x => fderiv ℝ p x (f x)) (alpha t) (v t)) t := by
  have hdp : DifferentiableAt ℝ (fderiv ℝ p) (alpha t) :=
    (hp.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hK := hdp.hasFDerivAt.clm_apply hf.hasFDerivAt
  have hsym := (hp.isSymmSndFDerivAt (by norm_num)).eq (f (alpha t)) (v t)
  have hd := (hdp.hasFDerivAt.comp_hasDerivAt t ha).clm_apply hv
  convert! hd using 1
  rw [hK.fderiv]
  change fderiv ℝ p (alpha t) (fderiv ℝ f (alpha t) (v t)) +
      fderiv ℝ (fderiv ℝ p) (alpha t) (v t) (f (alpha t)) = _
  rw [hsym, add_comm]
  rfl
