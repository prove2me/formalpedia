-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.CharacteristicFromRanks.mvExp_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:56:19.604156+00:00
-- url     : https://prove2.me/submissions/f8bf7fef-3614-4c8a-aedb-cf4c026fd877

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_Interface
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ExistsStrictMonoMinor
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CharacteristicFromRanks

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds
open Formalism.L2.FormalSeriesBounds.CharacteristicFromRanks
variable {C : Type} [Field C]
namespace Formalism.L2.FormalSeriesBounds.CharacteristicFromRanks
theorem _root_.solution {σ : Type} : mvExp (0 : MvPowerSeries σ C) = 1 := by
  refine MvPowerSeries.ext fun m => ?_
  show ∑ k ∈ Finset.range (m.degree + 1),
      MvPowerSeries.coeff m ((0 : MvPowerSeries σ C) ^ k) / (k.factorial : C) = MvPowerSeries.coeff m 1
  rw [Finset.sum_eq_single 0]
  · simp
  · intro k _ hk
    rw [zero_pow hk, map_zero, zero_div]
  · intro h
    simp at h
end Formalism.L2.FormalSeriesBounds.CharacteristicFromRanks
