-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.Z.inertFactor_sub_one_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:43:41.734881+00:00
-- url     : https://prove2.me/submissions/f9aad9bb-946e-4dfb-a8c0-120957f49e1b

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_FactorOverLocalSubalgebraMonic
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZReuse
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZCircleCharExtends
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_FactorOverLocalSubalgebra
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_CharpolyFactorAnnihilator
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZGoodCuspidal
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZBrauerNesbitt
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_CardLtAddCardGtAddCardEq
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_Z_norm_inert_cpow_eq
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_Z_half_le_norm_inert_denominator

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Filter Topology
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.Z
namespace Formalism.IrreducibleCountingLemmas.Z
theorem _root_.solution (q : ℝ) (ch s : ℂ) (hq : 2 ≤ q) (hch : ‖ch‖ = 1)
    (hs : 1 / 2 < s.re) : ‖inertFactor q ch s - 1‖ ≤ 4 * q ^ (-2 * s.re) := by
  have hd := half_le_norm_inert_denominator q ch s hq hch hs
  set u := ((q ^ 2 : ℝ) : ℂ) ^ (-s) with hu
  have hd0 : (1 - ch * u) ≠ 0 := by
    intro h; rw [h, norm_zero] at hd; linarith
  have e : inertFactor q ch s - 1 = (ch - 1) * u / (1 - ch * u) := by
    unfold inertFactor
    rw [← hu, div_sub_one hd0]
    congr 1
    ring
  rw [e, norm_div, norm_mul, hu, norm_inert_cpow_eq q s hq, ← hu]
  have h2 : ‖ch - 1‖ ≤ 2 := by
    have := norm_sub_le ch 1
    rw [hch, norm_one] at this; linarith
  have hp : 0 ≤ q ^ (-2 * s.re) := Real.rpow_nonneg (by linarith) _
  rw [div_le_iff₀ (by linarith)]
  calc ‖ch - 1‖ * q ^ (-2 * s.re) ≤ 2 * q ^ (-2 * s.re) := mul_le_mul_of_nonneg_right h2 hp
    _ = 4 * q ^ (-2 * s.re) * (1 / 2) := by ring
    _ ≤ 4 * q ^ (-2 * s.re) * ‖1 - ch * u‖ := mul_le_mul_of_nonneg_left hd (by positivity)
end Formalism.IrreducibleCountingLemmas.Z
