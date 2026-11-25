-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.rtj_mvExp_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:34:22.219741+00:00
-- url     : https://prove2.me/submissions/3561a5b7-e685-4209-ba49-1b961dcf5bd8

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_MemVarsProdAll
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieJet

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
variable {K : Type} [Field K] {σ τ : Type}
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution : mvExp (0 : MvPowerSeries σ K) = 1 := by
  ext m
  change (∑ k ∈ Finset.range (Finsupp.degree m + 1),
    MvPowerSeries.coeff m ((0 : MvPowerSeries σ K) ^ k) / (k.factorial : K)) = MvPowerSeries.coeff m 1
  rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr (Nat.succ_pos _))]
  · simp
  · intro k _ hk
    rw [zero_pow hk, map_zero, zero_div]
end Formalism.L2.FormalSeriesBounds
