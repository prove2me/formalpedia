-- Prove2me | solution 1 for Formalism.L2.Th1.B.Fs.ring_core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:03:05.422097+00:00
-- url     : https://prove2.me/submissions/94e72522-65d5-413d-9d32-bb2aebfa8548

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementD
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_RealAdelicInertTransportTypeFormsEqAlt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.Fs
open Formalism.InvariantFactorPaths.G7 (at1)
variable {K : Type} [Field K] [CharZero K]
local notation "A3" => MvPowerSeries (Fin 3) K
namespace Formalism.L2.Th1.B.Fs
theorem _root_.solution {R : Type} [CommRing R] (a b c M01 M02 M12 D01 D02 D12 t01 t02 t12 A DA : R)
    (T01 : (a - b) * D01 = M01 * (2 + 2 * (a - b) * t01))
    (T02 : (a - c) * D02 = M02 * (2 + 2 * (a - c) * t02))
    (T12 : (b - c) * D12 = M12 * (2 + 2 * (b - c) * t12))
    (hR : 2 * M01 * M02 * M12 * DA =
      A * (-D01 * M02 * M12 + D02 * M01 * M12 + 2 * D12 * M01 * M02)) :
    (2 * M01 * M02 * M12) *
        (A * ((a + b + c) * (-((a - c) * (b - c)) + (a - b) * (b - c) + 2 * ((a - b) * (a - c))) +
          (a + b + c) * (a - b) * (a - c) * (b - c) * (-t01 + t02 + 2 * t12))) =
      (2 * M01 * M02 * M12) * ((a + b + c) * (a - b) * (a - c) * (b - c) * DA) := by
  linear_combination (-((a + b + c) * (a - b) * (a - c) * (b - c))) * hR +
    A * M02 * M12 * (a + b + c) * (a - c) * (b - c) * T01 -
    A * M01 * M12 * (a + b + c) * (a - b) * (b - c) * T02 -
    2 * A * M01 * M02 * (a + b + c) * (a - b) * (a - c) * T12
end Formalism.L2.Th1.B.Fs
