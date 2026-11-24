-- Prove2me | solution 1 for Formalism.L2.Th1.B.Add1.wave_alg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:21:12.883182+00:00
-- url     : https://prove2.me/submissions/f1283d21-7df0-49d2-9cf1-e4f155339306

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementA
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_RestrictSecondZeroInVarOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.Add1
open Formalism.InvariantFactorPaths.G7 (at1)
variable {K : Type} [Field K] [CharZero K]
namespace Formalism.L2.Th1.B.Add1
theorem _root_.solution {R : Type} [CommRing R] (k a u v u1 u2 v1 v2 p0 p1 q0 q1 P0 P1 : R)
    (hW : P0 - P1 = 2 * k * (u - v))
    (h0 : (1 - k * u * v) * p0 = -(k * u1 * v))
    (h0' : -(k * u1 * v) * p0 + (1 - k * u * v) * q0 = -(k * u2 * v))
    (h1 : (1 - k * u * v) * p1 = -(k * u * v1))
    (h1' : -(k * u * v1) * p1 + (1 - k * u * v) * q1 = -(k * u * v2))
    (E1u : u1 ^ 2 = 4 * u + 4 * a * u ^ 2 + 4 * k * u ^ 3)
    (E1v : v1 ^ 2 = 4 * v + 4 * a * v ^ 2 + 4 * k * v ^ 3)
    (E2u : u2 = 2 + 4 * a * u + 6 * k * u ^ 2)
    (E2v : v2 = 2 + 4 * a * v + 6 * k * v ^ 2) :
    (1 - k * u * v) ^ 2 * (P0 - q0) = (1 - k * u * v) ^ 2 * (P1 - q1) := by
  linear_combination (1 - k * u * v) ^ 2 * hW - (1 - k * u * v) * h0' - (k * u1 * v) * h0
    + (1 - k * u * v) * h1' + (k * u * v1) * h1 + ((1 - k * u * v) * k * v) * E2u
    - ((1 - k * u * v) * k * u) * E2v + (k ^ 2 * v ^ 2) * E1u - (k ^ 2 * u ^ 2) * E1v
end Formalism.L2.Th1.B.Add1
