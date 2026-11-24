-- Prove2me | solution 1 for Formalism.L2.Th1.B.Add0.ring_core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:20:09.88238+00:00
-- url     : https://prove2.me/submissions/70b884a7-d18f-4a07-a497-09dbbc677c91

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementA
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_PderivZeroZeroWeierstrassDifference

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B
open Formalism.InvariantFactorPaths.G7 (at1)
open Formalism.L2.Th1.B.Add0
variable {K : Type} [Field K] [CharZero K]
local notation "A2" => MvPowerSeries (Fin 2) K
namespace Formalism.L2.Th1.B.Add0
theorem _root_.solution {R : Type} [CommRing R] (a b p r p1 r1 p2 r2 h g3 : R)
    (F1a : a ^ 4 * p1 ^ 2 - 4 * a * p1 = 12 * p + 12 * a ^ 2 * p ^ 2 + 4 * a ^ 4 * p ^ 3 -
      (2 * h) * a ^ 2 * (1 + a ^ 2 * p) - g3 * a ^ 4)
    (KoszulLowersPower : a ^ 2 * p2 = 12 * p + 6 * a ^ 2 * p ^ 2 - h * a ^ 2)
    (AutomorphicLevelEquivariance : b ^ 4 * r1 ^ 2 - 4 * b * r1 = 12 * r + 12 * b ^ 2 * r ^ 2 + 4 * b ^ 4 * r ^ 3 -
      (2 * h) * b ^ 2 * (1 + b ^ 2 * r) - g3 * b ^ 4)
    (KoszulImageInIdeal : b ^ 2 * r2 = 12 * r + 6 * b ^ 2 * r ^ 2 - h * b ^ 2) :
    (a ^ 2 - b ^ 2 + a ^ 2 * b ^ 2 * (r - p)) *
      ((2 + 2 * b ^ 2 * (r - p) - 4 * a * b ^ 2 * p1 - a ^ 2 * b ^ 2 * p2) -
        (-2 + 2 * a ^ 2 * (r - p) + 4 * a ^ 2 * b * r1 + a ^ 2 * b ^ 2 * r2)) -
      (2 * a + 2 * a * b ^ 2 * (r - p) - a ^ 2 * b ^ 2 * p1) ^ 2 +
      (-2 * b + 2 * a ^ 2 * b * (r - p) + a ^ 2 * b ^ 2 * r1) ^ 2 =
    (2 * p - 2 * r) * (a ^ 2 - b ^ 2 + a ^ 2 * b ^ 2 * (r - p)) ^ 2 := by
  linear_combination (-b ^ 4) * F1a + (-(a ^ 2 - b ^ 2 + a ^ 2 * b ^ 2 * (r - p)) * b ^ 2) * KoszulLowersPower +
    (a ^ 4) * AutomorphicLevelEquivariance + (-(a ^ 2 - b ^ 2 + a ^ 2 * b ^ 2 * (r - p)) * a ^ 2) * KoszulImageInIdeal
end Formalism.L2.Th1.B.Add0
