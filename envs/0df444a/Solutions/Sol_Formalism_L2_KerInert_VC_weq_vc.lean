-- Prove2me | solution 1 for Formalism.L2.KerInert.VC.weq_vc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:40:07.394649+00:00
-- url     : https://prove2.me/submissions/fc7b4d59-f512-42ec-b613-e4bbfb4ae27c

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
    (U^3*w*v) = (U*(u - r*w)*v)^3 + (Ui*(a1+2*s))*(U*(u - r*w)*v)*(U^3*w*v) + (Ui^2*(a2 - s*a1 + 3*r - s^2))*(U*(u - r*w)*v)^2*(U^3*w*v) + (Ui^3*(a3 + r*a1 + 2*t))*(U^3*w*v)^2 + (Ui^4*(a4 - s*a3 + 2*r*a2 - (t + r*s)*a1 + 3*r^2 - 2*s*t))*(U*(u - r*w)*v)*(U^3*w*v)^2 + (Ui^6*(a6 + r*a4 + r^2*a2 + r^3 - t*a3 - t^2 - r*t*a1))*(U^3*w*v)^3 := by
  linear_combination (U^3*v^3*(1)) * hw + (U^3*(v^3*((-a1*r*s*u*w^2 + a1*s*u^2*w + a1*t*u*w^2 - a2*u^2*w - a3*r*s*w^3 + a3*s*u*w^2 + a3*t*w^3 - a4*u*w^2 - a6*w^3 + r^2*s^2*w^3 - 2*r*s^2*u*w^2 - 2*r*s*t*w^3 + s^2*u^2*w + 2*s*t*u*w^2 + t^2*w^3 - u^3)*(1 + s*u + (t - s*r)*w)^0*((v*(1 + s*u + (t - s*r)*w))^0 + (v*(1 + s*u + (t - s*r)*w))^1 + (v*(1 + s*u + (t - s*r)*w))^2) + (-a1*u*w - a3*w^2 + 2*r*s*w^2 - 2*s*u*w - 2*t*w^2)*(1 + s*u + (t - s*r)*w)^1*((v*(1 + s*u + (t - s*r)*w))^0 + (v*(1 + s*u + (t - s*r)*w))^1) + (w)*(1 + s*u + (t - s*r)*w)^2*((v*(1 + s*u + (t - s*r)*w))^0)) - (-a1*r*s*u*v^3*w^2 + a1*s*u^2*v^3*w + a1*t*u*v^3*w^2 - a1*u*v^2*w - a2*u^2*v^3*w - a3*r*s*v^3*w^3 + a3*s*u*v^3*w^2 + a3*t*v^3*w^3 - a3*v^2*w^2 - a4*u*v^3*w^2 - a6*v^3*w^3 + r^2*s^2*v^3*w^3 - 2*r*s^2*u*v^3*w^2 - 2*r*s*t*v^3*w^3 + 2*r*s*v^2*w^2 + s^2*u^2*v^3*w + 2*s*t*u*v^3*w^2 - 2*s*u*v^2*w + t^2*v^3*w^3 - 2*t*v^2*w^2 - u^3*v^3 + v*w)*((v*(1 + s*u + (t - s*r)*w))^0 + (v*(1 + s*u + (t - s*r)*w))^1 + (v*(1 + s*u + (t - s*r)*w))^2))) * hv + (U^3*(a1*r*t*v^3*w^3 - a2*r^2*v^3*w^3 + a3*t*v^3*w^3 - a4*r*v^3*w^3 - a6*v^3*w^3 - r^3*v^3*w^3 + t^2*v^3*w^3)*((U*Ui)^0 + (U*Ui)^1 + (U*Ui)^2 + (U*Ui)^3 + (U*Ui)^4 + (U*Ui)^5) + U^3*(-a1*r^2*s*v^3*w^3 + a1*r*s*u*v^3*w^2 - a1*r*t*v^3*w^3 + a1*t*u*v^3*w^2 + 2*a2*r^2*v^3*w^3 - 2*a2*r*u*v^3*w^2 - a3*r*s*v^3*w^3 + a3*s*u*v^3*w^2 + a4*r*v^3*w^3 - a4*u*v^3*w^2 + 3*r^3*v^3*w^3 - 3*r^2*u*v^3*w^2 - 2*r*s*t*v^3*w^3 + 2*s*t*u*v^3*w^2)*((U*Ui)^0 + (U*Ui)^1 + (U*Ui)^2 + (U*Ui)^3) + U^3*(-a1*r*v^2*w^2 - a3*v^2*w^2 - 2*t*v^2*w^2)*((U*Ui)^0 + (U*Ui)^1 + (U*Ui)^2) + U^3*(a1*r^2*s*v^3*w^3 - 2*a1*r*s*u*v^3*w^2 + a1*s*u^2*v^3*w - a2*r^2*v^3*w^3 + 2*a2*r*u*v^3*w^2 - a2*u^2*v^3*w - 3*r^3*v^3*w^3 + r^2*s^2*v^3*w^3 + 6*r^2*u*v^3*w^2 - 2*r*s^2*u*v^3*w^2 - 3*r*u^2*v^3*w + s^2*u^2*v^3*w)*((U*Ui)^0 + (U*Ui)^1) + U^3*(a1*r*v^2*w^2 - a1*u*v^2*w + 2*r*s*v^2*w^2 - 2*s*u*v^2*w)*((U*Ui)^0)) * hU
end Formalism.L2.KerInert.VC
