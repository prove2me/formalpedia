-- Prove2me | solution 1 for BianchiIX.hasDerivAt_coordinate_variation
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T22:42:40.287513+00:00
-- url     : https://prove2.me/submissions/08f376ef-e514-4d91-bb7a-204cbdfc769a

import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.NormNum


namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX
open Filter
open scoped Topology
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]


/-- A local parameterized family suffices; the coordinate map need not be invertible in ambient space. -/
theorem solution
    {p : E → F} {f : E → E} {g : F → F} {alpha v : ℝ → E} {t : ℝ}
    (hp : ContDiffAt ℝ 2 p (alpha t)) (hf : DifferentiableAt ℝ f (alpha t))
    (hg : DifferentiableAt ℝ g (p (alpha t)))
    (ha : HasDerivAt alpha (f (alpha t)) t)
    (hv : HasDerivAt v (fderiv ℝ f (alpha t) (v t)) t)
    {b : G → E} {B : G →L[ℝ] E} {z w : G}
    (hb : HasFDerivAt b B z) (hbz : b z = alpha t) (hBw : B w = v t)
    (heq : (fun q => fderiv ℝ p (b q) (f (b q))) =ᶠ[𝓝 z] (fun q => g (p (b q)))) :
    HasDerivAt (fun s => fderiv ℝ p (alpha s) (v s))
      (fderiv ℝ g (p (alpha t)) (fderiv ℝ p (alpha t) (v t))) t := by
  have hdp : DifferentiableAt ℝ (fderiv ℝ p) (alpha t) :=
    (hp.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hp' := hp.differentiableAt (by norm_num)
  have hK := hdp.hasFDerivAt.clm_apply hf.hasFDerivAt
  have hleft := (hbz.symm ▸ hK).comp z hb
  have hright' : HasFDerivAt (fun q => g (p (b q)))
      ((fderiv ℝ g (p (alpha t))).comp ((fderiv ℝ p (alpha t)).comp B)) z := by
    convert! (hbz.symm ▸ (hg.hasFDerivAt.comp (alpha t) hp'.hasFDerivAt)).comp z hb using 1
    rw [hbz, ContinuousLinearMap.comp_assoc]
  have hid := congrArg (fun L : G →L[ℝ] F => L w)
    ((hleft.congr_of_eventuallyEq heq.symm).unique hright')
  have hsym := (hp.isSymmSndFDerivAt (by norm_num)).eq (f (alpha t)) (v t)
  have hd := (hdp.hasFDerivAt.comp_hasDerivAt t ha).clm_apply hv
  convert! hd using 1
  change fderiv ℝ g (p (alpha t)) (fderiv ℝ p (alpha t) (v t)) =
    fderiv ℝ (fderiv ℝ p) (alpha t) (f (alpha t)) (v t) +
      fderiv ℝ p (alpha t) (fderiv ℝ f (alpha t) (v t))
  rw [hsym, add_comm]
  simp only [ContinuousLinearMap.comp_apply, hbz, hBw] at hid
  exact hid.symm
