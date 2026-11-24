-- Prove2me | solution 1 for Formalism.L2.Th1.B.Fs.fExp_three
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:00:58.417367+00:00
-- url     : https://prove2.me/submissions/7c0a9e33-6853-4692-93e3-f37dd3ca4225

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementD
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_RealAdelicInertTransportTypeFormsEqAlt
import Theorems.Thm_Formalism_L2_Th1_B_fExp_add


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
namespace Formalism.L2.Th1.B.Fs
theorem _root_.solution {K : Type} [Field K] [CharZero K] {ι : Type} {f : MvPowerSeries ι K}
    (hf : MvPowerSeries.constantCoeff f = 0) : fExp f ^ 3 = fExp (3 * f) := by
  have h3 : 3 * f = f + f + f := by ring
  rw [h3, fExp_add (by rw [map_add, hf, add_zero]) hf, fExp_add hf hf]
  ring
end Formalism.L2.Th1.B.Fs
