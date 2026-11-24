-- Prove2me | solution 1 for Formalism.L2.Th1.B.Det.core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:02:59.191176+00:00
-- url     : https://prove2.me/submissions/5b6255cc-1185-4e0a-a43c-19bf0263bd22

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementD
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_Wp3ApplyEqSqMulSubSqMul

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
set_option maxHeartbeats 400000
namespace Formalism.L2.Th1.B.Det
theorem _root_.solution {R : Type} [CommRing R] (a b c Xa Ya Xb Yb Xc Yc h g3 : R)
    (Ca : Ya ^ 2 = 4 * Xa ^ 3 - 2 * h * a ^ 4 * Xa - g3 * a ^ 6)
    (Cb : Yb ^ 2 = 4 * Xb ^ 3 - 2 * h * b ^ 4 * Xb - g3 * b ^ 6)
    (Cc : Yc ^ 2 = 4 * Xc ^ 3 - 2 * h * c ^ 4 * Xc - g3 * c ^ 6) :
    2 * (a ^ 2 * Xb - b ^ 2 * Xa) * (a ^ 2 * Xc - c ^ 2 * Xa) * (b ^ 2 * Xc - c ^ 2 * Xb) * a *
      (c * (a ^ 3 * (b * (3 * Xb + Yb) * Yc - (6 * Xb ^ 2 - h * b ^ 4 + 3 * Yb) * (c * Xc)) -
          a * Xa * (3 * b ^ 3 * Yc - (6 * Xb ^ 2 - h * b ^ 4 + 3 * Yb) * c ^ 3) +
          Ya * (3 * b ^ 3 * (c * Xc) - b * (3 * Xb + Yb) * c ^ 3)) -
        b * (a ^ 3 * (b * Xb * (6 * Xc ^ 2 - h * c ^ 4 + 3 * Yc) - Yb * (c * (3 * Xc + Yc))) -
          a * Xa * (b ^ 3 * (6 * Xc ^ 2 - h * c ^ 4 + 3 * Yc) - Yb * (3 * c ^ 3)) +
          Ya * (b ^ 3 * (c * (3 * Xc + Yc)) - b * Xb * (3 * c ^ 3)))) =
    (a ^ 3 * (b * Xb * Yc - Yb * (c * Xc)) - a * Xa * (b ^ 3 * Yc - Yb * c ^ 3) +
        Ya * (b ^ 3 * (c * Xc) - b * Xb * c ^ 3)) *
      (-c * (b * (2 * a ^ 2 * Xb - b ^ 2 * (Ya + 2 * Xa)) -
            a * (a ^ 2 * (Yb + 2 * Xb) - 2 * b ^ 2 * Xa)) *
          (a ^ 2 * Xc - c ^ 2 * Xa) * (b ^ 2 * Xc - c ^ 2 * Xb) +
        b * (c * (2 * a ^ 2 * Xc - c ^ 2 * (Ya + 2 * Xa)) -
            a * (a ^ 2 * (Yc + 2 * Xc) - 2 * c ^ 2 * Xa)) *
          (a ^ 2 * Xb - b ^ 2 * Xa) * (b ^ 2 * Xc - c ^ 2 * Xb) +
        2 * a * (c * (2 * b ^ 2 * Xc - c ^ 2 * (Yb + 2 * Xb)) -
            b * (b ^ 2 * (Yc + 2 * Xc) - 2 * c ^ 2 * Xb)) *
          (a ^ 2 * Xb - b ^ 2 * Xa) * (a ^ 2 * Xc - c ^ 2 * Xa)) := by
  linear_combination (-a^2*b^2*c^2*(-Xb*c^2 + Xc*b^2)^3) * Ca + (a^2*c^2*(-Xa*c^2 + Xc*a^2)^2*(2*Xa*b^2*c^2 - 3*Xb*a^2*c^2 + Xc*a^2*b^2)) * Cb +
    (a^2*b^2*(-Xa*b^2 + Xb*a^2)^2*(-2*Xa*b^2*c^2 - Xb*a^2*c^2 + 3*Xc*a^2*b^2)) * Cc
end Formalism.L2.Th1.B.Det
