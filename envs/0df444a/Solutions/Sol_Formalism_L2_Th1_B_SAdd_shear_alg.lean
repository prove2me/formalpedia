-- Prove2me | solution 1 for Formalism.L2.Th1.B.SAdd.shear_alg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:04:09.16586+00:00
-- url     : https://prove2.me/submissions/2d7480eb-bea7-45b1-b84d-695be1aa143e

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementE
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_ConstantCoeffQuotientXSq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.SAdd
open Formalism.InvariantFactorPaths.G7 (at1)
variable {K : Type} [Field K] [CharZero K]
namespace Formalism.L2.Th1.B.SAdd
theorem _root_.solution {R : Type} [CommRing R] (k a x y x1 y1 : R)
    (hx : x1 ^ 2 = 1 + a * x ^ 2 + k * (x ^ 2) ^ 2)
    (hy : y1 ^ 2 = 1 + a * y ^ 2 + k * (y ^ 2) ^ 2) :
    (1 - k * x ^ 2 * y ^ 2) *
        (y * ((a + 2 * k * x ^ 2) * x) - x * ((a + 2 * k * y ^ 2) * y)) =
      (x * y1 + y * x1) *
        (-(k * (2 * x * x1) * y ^ 2) + k * x ^ 2 * (2 * y * y1)) := by
  linear_combination (2 * k * x * y * y ^ 2) * hx - (2 * k * x * y * x ^ 2) * hy
end Formalism.L2.Th1.B.SAdd
