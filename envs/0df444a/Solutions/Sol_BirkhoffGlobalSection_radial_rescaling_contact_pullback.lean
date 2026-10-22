-- Prove2me | solution 1 for BirkhoffGlobalSection.radial_rescaling_contact_pullback
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-30T17:02:51.107223+00:00
-- url     : https://prove2.me/submissions/47c62174-ed4f-432b-852a-16e6c2a47ad5

import Definitions.Def_BirkhoffGlobalSection_TransverseHopf
import Mathlib.Analysis.Calculus.FDeriv.Mul

open BirkhoffGlobalSection

/-- The radial primitive pulls back under a variable radial rescaling by the
square of the scale. The derivative of the scale contributes only a radial
vector, annihilated by the primitive. This is the ambient identity underlying
Hryniewicz's star-shaped sphere pullback formula (arXiv:1105.2077v5, p. 2). -/
theorem solution (a : Phase → ℝ) (y v : Phase)
    (ha : DifferentiableAt ℝ a y) :
    phaseRadialContact (a y • y)
      (fderiv ℝ (fun x : Phase => a x • x) y v) =
        (a y) ^ 2 * phaseRadialContact y v := by
  have hid : DifferentiableAt ℝ (fun x : Phase => x) y := differentiableAt_id
  rw [fderiv_fun_smul ha hid]
  simp only [Pi.smul_apply, smul_eq_mul, phaseRadialContact, phaseSymplecticForm,
    add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, fderiv_fun_id, ContinuousLinearMap.id_apply,
    Pi.add_apply]
  ring
