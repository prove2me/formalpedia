-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.TW.UnitBall.exists_nat_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:51:41.052175+00:00
-- url     : https://prove2.me/submissions/058c862a-ee4a-4dd4-8747-ad33cb78816e

import Mathlib
import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_CentralIdempotentIntegral
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_TWUnitBallLattice
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_TW_UnitBall_norm_unif_pos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.TW
open Formalism.IrreducibleCountingLemmas.TW.UnitBall
variable {K : Type} [NontriviallyNormedField K] [IsUltrametricDist K]
namespace Formalism.IrreducibleCountingLemmas.TW.UnitBall
theorem _root_.solution (ϖ : K) (h1 : ‖ϖ‖ < 1) (hd : ∀ x : K, x ≠ 0 → ∃ n : ℤ, ‖x‖ = ‖ϖ‖ ^ n)
    (x : K) (hx0 : x ≠ 0) (hx : ‖x‖ ≤ 1) : ∃ n : ℕ, ‖x‖ = ‖ϖ‖ ^ n := by
  have h0 := norm_unif_pos ϖ hd
  obtain ⟨n, hn⟩ := hd x hx0
  have hn0 : 0 ≤ n := by
    by_contra h
    have := one_lt_zpow_of_neg₀ h0 h1 (not_le.mp h)
    linarith
  refine ⟨n.toNat, ?_⟩
  rw [hn, ← zpow_natCast, Int.toNat_of_nonneg hn0]
end Formalism.IrreducibleCountingLemmas.TW.UnitBall
