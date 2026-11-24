-- Prove2me | solution 1 for Formalism.L2.Th1.B.Det.core2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:13:23.346803+00:00
-- url     : https://prove2.me/submissions/517da25e-bc6c-4873-8ffa-bffef073e158

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementD
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_Wp3ApplyEqSqMulSubSqMul
import Theorems.Thm_Formalism_L2_Th1_B_Det_core

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.Det
open Formalism.InvariantFactorPaths.G7 (at1)
namespace Formalism.L2.Th1.B.Det
theorem _root_.solution {R : Type} [CommRing R] (a b c Xa Ya Xb Yb Xc Yc h g3 dXa dXb dXc dYb dYc : R)
    (Ca : Ya ^ 2 = 4 * Xa ^ 3 - 2 * h * a ^ 4 * Xa - g3 * a ^ 6)
    (Cb : Yb ^ 2 = 4 * Xb ^ 3 - 2 * h * b ^ 4 * Xb - g3 * b ^ 6)
    (Cc : Yc ^ 2 = 4 * Xc ^ 3 - 2 * h * c ^ 4 * Xc - g3 * c ^ 6)
    (ha : a * dXa = Ya + 2 * Xa) (hb : b * dXb = Yb + 2 * Xb) (hc : c * dXc = Yc + 2 * Xc)
    (kb : b * dYb = 6 * Xb ^ 2 - h * b ^ 4 + 3 * Yb)
    (kc : c * dYc = 6 * Xc ^ 2 - h * c ^ 4 + 3 * Yc) :
    (a * b * c) * (2 * (a ^ 2 * Xb - b ^ 2 * Xa) * (a ^ 2 * Xc - c ^ 2 * Xa) *
        (b ^ 2 * Xc - c ^ 2 * Xb) *
      ((a ^ 3 * ((Xb + b * dXb) * Yc - dYb * (c * Xc)) -
          a * Xa * (3 * b ^ 2 * Yc - dYb * c ^ 3) +
          Ya * (3 * b ^ 2 * (c * Xc) - (Xb + b * dXb) * c ^ 3)) -
        (a ^ 3 * (b * Xb * dYc - Yb * (Xc + c * dXc)) -
          a * Xa * (b ^ 3 * dYc - Yb * (3 * c ^ 2)) +
          Ya * (b ^ 3 * (Xc + c * dXc) - b * Xb * (3 * c ^ 2))))) =
    (a * b * c) * ((a ^ 3 * (b * Xb * Yc - Yb * (c * Xc)) - a * Xa * (b ^ 3 * Yc - Yb * c ^ 3) +
        Ya * (b ^ 3 * (c * Xc) - b * Xb * c ^ 3)) *
      (-((2 * a * Xb - b ^ 2 * dXa) - (a ^ 2 * dXb - 2 * b * Xa)) *
          (a ^ 2 * Xc - c ^ 2 * Xa) * (b ^ 2 * Xc - c ^ 2 * Xb) +
        ((2 * a * Xc - c ^ 2 * dXa) - (a ^ 2 * dXc - 2 * c * Xa)) *
          (a ^ 2 * Xb - b ^ 2 * Xa) * (b ^ 2 * Xc - c ^ 2 * Xb) +
        2 * ((2 * b * Xc - c ^ 2 * dXb) - (b ^ 2 * dXc - 2 * c * Xb)) *
          (a ^ 2 * Xb - b ^ 2 * Xa) * (a ^ 2 * Xc - c ^ 2 * Xa))) := by
  linear_combination (-a^2*b*c*(-Xb*c^2 + Xc*b^2)^2*(Xa*Yb*a*c^3 - Xa*Yc*a*b^3 - Xb*Ya*b*c^3 + Xb*Yc*a^3*b + Xc*Ya*b^3*c - Xc*Yb*a^3*c)) * ha +
    (a^2*c*(-Xa*c^2 + Xc*a^2)*(-2*Xa^2*Yb*b^2*c^5 + 2*Xa^2*Yc*b^5*c^2 + 3*Xa*Xb*Yb*a^2*c^5 - 3*Xa*Xb*Yc*a^2*b^3*c^2 + Xa*Xc*Yb*a^2*b^2*c^3 - Xa*Xc*Yc*a^2*b^5 - Xb^2*Ya*a*b*c^5 + Xb^2*Yc*a^4*b*c^2 + 2*Xb*Xc*Ya*a*b^3*c^3 - 3*Xb*Xc*Yb*a^4*c^3 + Xb*Xc*Yc*a^4*b^3 - Xc^2*Ya*a*b^5*c + Xc^2*Yb*a^4*b^2*c)) * hb +
    (a^2*b*(-Xa*b^2 + Xb*a^2)*(-2*Xa^2*Yb*b^2*c^5 + 2*Xa^2*Yc*b^5*c^2 + Xa*Xb*Yb*a^2*c^5 - Xa*Xb*Yc*a^2*b^3*c^2 + 3*Xa*Xc*Yb*a^2*b^2*c^3 - 3*Xa*Xc*Yc*a^2*b^5 + Xb^2*Ya*a*b*c^5 - Xb^2*Yc*a^4*b*c^2 - 2*Xb*Xc*Ya*a*b^3*c^3 - Xb*Xc*Yb*a^4*c^3 + 3*Xb*Xc*Yc*a^4*b^3 + Xc^2*Ya*a*b^5*c - Xc^2*Yb*a^4*b^2*c)) * hc +
    (-2*a^2*c^2*(-Xa*b^2 + Xb*a^2)*(-Xa*c^2 + Xc*a^2)^2*(-Xb*c^2 + Xc*b^2)) * kb + (-2*a^2*b^2*(-Xa*b^2 + Xb*a^2)^2*(-Xa*c^2 + Xc*a^2)*(-Xb*c^2 + Xc*b^2)) * kc +
    core a b c Xa Ya Xb Yb Xc Yc h g3 Ca Cb Cc
end Formalism.L2.Th1.B.Det
