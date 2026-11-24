-- Prove2me | solution 1 for Formalism.L2.Th1.B.SAdd.atS_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:04:05.048504+00:00
-- url     : https://prove2.me/submissions/6664e6a8-4f01-4ec2-801f-bf08e5f8eca3

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
theorem _root_.solution (f : PowerSeries K) : atS (f ^ 2) = atS f ^ 2 := by
  have hs : PowerSeries.HasSubst
      (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by simp)
  rw [atS, atS, ← PowerSeries.coe_substAlgHom hs, map_pow]
end Formalism.L2.Th1.B.SAdd
