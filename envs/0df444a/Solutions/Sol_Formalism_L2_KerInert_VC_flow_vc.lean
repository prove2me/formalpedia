-- Prove2me | solution 1 for Formalism.L2.KerInert.VC.flow_vc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:41:26.651264+00:00
-- url     : https://prove2.me/submissions/00349fba-9404-44f2-ab97-90623a3f9f68

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowTwoTorsionWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Points
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_CurveEndoAll
import Definitions.Def_Formalism_LocalToGlobal_InertKernelTheory_InertCoprimeLemmas_VarChange
import Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_hv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
noncomputable section
open Formalism Formalism.L2 Formalism.L2.KerInert Formalism.L2.KerInert.VC
variable {A : Type*} [CommRing A] (a1 a2 a3 a4 a6 U Ui r s t u w v : A)
namespace Formalism.L2.KerInert.VC
theorem _root_.solution (hw : w = u^3 + a1*u*w + a2*u^2*w + a3*w^2 + a4*u*w^2 + a6*w^3)
    (hv : v * (1 + s*u + (t - s*r)*w) = 1) (hU : U * Ui = 1) :
    U*(((1 - a1*u - a2*u^2 - 2*a3*w - 2*a4*u*w - 3*a6*w^2) - r*(3*u^2 + a1*w + 2*a2*u*w + a4*w^2))*v + (u - r*w)*(-v^2*(s*(1 - a1*u - a2*u^2 - 2*a3*w - 2*a4*u*w - 3*a6*w^2) + (t - s*r)*(3*u^2 + a1*w + 2*a2*u*w + a4*w^2)))) =
      U*(1 - (Ui*(a1+2*s))*(U*(u - r*w)*v) - (Ui^2*(a2 - s*a1 + 3*r - s^2))*(U*(u - r*w)*v)^2 - 2*(Ui^3*(a3 + r*a1 + 2*t))*(U^3*w*v) - 2*(Ui^4*(a4 - s*a3 + 2*r*a2 - (t + r*s)*a1 + 3*r^2 - 2*s*t))*(U*(u - r*w)*v)*(U^3*w*v) - 3*(Ui^6*(a6 + r*a4 + r^2*a2 + r^3 - t*a3 - t^2 - r*t*a1))*(U^3*w*v)^2) := by
  linear_combination (U^1*v^2*(3*t)) * hw + (U^1*(v^2*((-3*a1*t*u*w - 2*a2*r^2*s*u*w^2 + a2*r*s*u^2*w + 2*a2*r*t*u*w^2 + 2*a2*r*u*w + a2*s*u^3 - 2*a2*t*u^2*w + a2*u^2 - 3*a3*t*w^2 - a4*r^2*s*w^3 - a4*r*s*u*w^2 + a4*r*t*w^3 + a4*r*w^2 + 2*a4*s*u^2*w - a4*t*u*w^2 + 2*a4*u*w - 3*a6*r*s*w^3 + 3*a6*s*u*w^2 + 3*a6*w^2 - r^2*s^2*w^2 - 3*r^2*s*u^2*w + 2*r*s^2*u*w + 4*r*s*t*w^2 + 3*r*s*u^3 + r*s*w + 3*r*t*u^2*w + 3*r*u^2 - s^2*u^2 - 4*s*t*u*w - s*u - 3*t^2*w^2 - 3*t*u^3)*(1 + s*u + (t - s*r)*w)^0*((v*(1 + s*u + (t - s*r)*w))^0 + (v*(1 + s*u + (t - s*r)*w))^1) + (-2*a2*r*u*w - a2*u^2 - a4*r*w^2 - 2*a4*u*w - 3*a6*w^2 - 2*r*s*w - 3*r*u^2 + 2*s*u + 4*t*w + 1)*(1 + s*u + (t - s*r)*w)^1*((v*(1 + s*u + (t - s*r)*w))^0)) - (-3*a1*t*u*v^2*w - 2*a2*r^2*s*u*v^2*w^2 + a2*r*s*u^2*v^2*w + 2*a2*r*t*u*v^2*w^2 + 2*a2*r*u*v^2*w - 2*a2*r*u*v*w + a2*s*u^3*v^2 - 2*a2*t*u^2*v^2*w + a2*u^2*v^2 - a2*u^2*v - 3*a3*t*v^2*w^2 - a4*r^2*s*v^2*w^3 - a4*r*s*u*v^2*w^2 + a4*r*t*v^2*w^3 + a4*r*v^2*w^2 - a4*r*v*w^2 + 2*a4*s*u^2*v^2*w - a4*t*u*v^2*w^2 + 2*a4*u*v^2*w - 2*a4*u*v*w - 3*a6*r*s*v^2*w^3 + 3*a6*s*u*v^2*w^2 + 3*a6*v^2*w^2 - 3*a6*v*w^2 - r^2*s^2*v^2*w^2 - 3*r^2*s*u^2*v^2*w + 2*r*s^2*u*v^2*w + 4*r*s*t*v^2*w^2 + 3*r*s*u^3*v^2 + r*s*v^2*w - 2*r*s*v*w + 3*r*t*u^2*v^2*w + 3*r*u^2*v^2 - 3*r*u^2*v - s^2*u^2*v^2 - 4*s*t*u*v^2*w - s*u*v^2 + 2*s*u*v - 3*t^2*v^2*w^2 - 3*t*u^3*v^2 + 4*t*v*w + v - 1)*((v*(1 + s*u + (t - s*r)*w))^0 + (v*(1 + s*u + (t - s*r)*w))^1))) * hv + (U^1*(-3*a1*r*t*v^2*w^2 + 3*a2*r^2*v^2*w^2 - 3*a3*t*v^2*w^2 + 3*a4*r*v^2*w^2 + 3*a6*v^2*w^2 + 3*r^3*v^2*w^2 - 3*t^2*v^2*w^2)*((U*Ui)^0 + (U*Ui)^1 + (U*Ui)^2 + (U*Ui)^3 + (U*Ui)^4 + (U*Ui)^5) + U^1*(2*a1*r^2*s*v^2*w^2 - 2*a1*r*s*u*v^2*w + 2*a1*r*t*v^2*w^2 - 2*a1*t*u*v^2*w - 4*a2*r^2*v^2*w^2 + 4*a2*r*u*v^2*w + 2*a3*r*s*v^2*w^2 - 2*a3*s*u*v^2*w - 2*a4*r*v^2*w^2 + 2*a4*u*v^2*w - 6*r^3*v^2*w^2 + 6*r^2*u*v^2*w + 4*r*s*t*v^2*w^2 - 4*s*t*u*v^2*w)*((U*Ui)^0 + (U*Ui)^1 + (U*Ui)^2 + (U*Ui)^3) + U^1*(2*a1*r*v*w + 2*a3*v*w + 4*t*v*w)*((U*Ui)^0 + (U*Ui)^1 + (U*Ui)^2) + U^1*(-a1*r^2*s*v^2*w^2 + 2*a1*r*s*u*v^2*w - a1*s*u^2*v^2 + a2*r^2*v^2*w^2 - 2*a2*r*u*v^2*w + a2*u^2*v^2 + 3*r^3*v^2*w^2 - r^2*s^2*v^2*w^2 - 6*r^2*u*v^2*w + 2*r*s^2*u*v^2*w + 3*r*u^2*v^2 - s^2*u^2*v^2)*((U*Ui)^0 + (U*Ui)^1) + U^1*(-a1*r*v*w + a1*u*v - 2*r*s*v*w + 2*s*u*v)*((U*Ui)^0)) * hU
end Formalism.L2.KerInert.VC
