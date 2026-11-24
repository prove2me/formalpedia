-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.Z.half_le_norm_inert_denominator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:24:20.531519+00:00
-- url     : https://prove2.me/submissions/7678a8a1-bb82-47d8-be6f-109caeec139c

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_FactorOverLocalSubalgebraMonic
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZReuse
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZCircleCharExtends
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_FactorOverLocalSubalgebra
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_CharpolyFactorAnnihilator
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZGoodCuspidal
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZBrauerNesbitt
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_CardLtAddCardGtAddCardEq
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_Z_norm_inert_cpow_eq
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_Z_rpow_neg_two_mul_le_half

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
theorem _root_.solution (q : ℝ) (ch s : ℂ) (hq : 2 ≤ q) (hch : ‖ch‖ = 1) (hs : 1 / 2 < s.re) :
    1 / 2 ≤ ‖1 - ch * ((q ^ 2 : ℝ) : ℂ) ^ (-s)‖ := by
  have h1 : ‖ch * ((q ^ 2 : ℝ) : ℂ) ^ (-s)‖ ≤ 1 / 2 := by
    rw [norm_mul, hch, one_mul, norm_inert_cpow_eq q s hq]; exact rpow_neg_two_mul_le_half q _ hq hs
  have h2 := norm_sub_norm_le (1 : ℂ) (ch * ((q ^ 2 : ℝ) : ℂ) ^ (-s))
  rw [norm_one] at h2
  linarith
end Formalism.IrreducibleCountingLemmas.Z
