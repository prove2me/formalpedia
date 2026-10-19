-- Prove2me | solution 1 for CohnElkies.complexDigamma_continuousOn_positiveHalfPlane
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:32.057836+00:00
-- url     : https://prove2.me/submissions/9de2f577-dff4-4bb9-83f0-5aa6dd920314

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_complexGamma_differentiableOn_positiveHalfPlane

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology BigOperators
namespace CohnElkies
theorem _root_.solution :
    ContinuousOn Complex.digamma
      {z : ℂ | 0 < z.re} := by
  let s : Set ℂ := {z : ℂ | 0 < z.re}
  have hopen : IsOpen s := by
    exact Complex.continuous_re.isOpen_preimage _ isOpen_Ioi
  have hgamma : DifferentiableOn ℂ Complex.Gamma s :=
    complexGamma_differentiableOn_positiveHalfPlane
  have hderiv : ContinuousOn (deriv Complex.Gamma) s :=
    (hgamma.deriv hopen).continuousOn
  have hcont : ContinuousOn Complex.Gamma s :=
    hgamma.continuousOn
  have hratio :
      ContinuousOn
        (fun z : ℂ => deriv Complex.Gamma z /
          Complex.Gamma z) s :=
    hderiv.div hcont
      (fun z hz =>
        Complex.Gamma_ne_zero_of_re_pos hz)
  simpa [s, Complex.digamma_def, logDeriv_apply] using! hratio
end CohnElkies
