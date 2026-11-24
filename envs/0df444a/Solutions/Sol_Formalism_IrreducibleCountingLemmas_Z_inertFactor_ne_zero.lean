-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.Z.inertFactor_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:53:26.039346+00:00
-- url     : https://prove2.me/submissions/370a128e-a358-4988-ab7d-2813bb28fe1a

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_FactorOverLocalSubalgebraMonic
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZReuse
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZCircleCharExtends
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_FactorOverLocalSubalgebra
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_CharpolyFactorAnnihilator
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZGoodCuspidal
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZBrauerNesbitt
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_CardLtAddCardGtAddCardEq
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
    (hs : 1 / 2 < s.re) : inertFactor q ch s ≠ 0 := by
  have hd := half_le_norm_inert_denominator q ch s hq hch hs
  have hn := half_le_norm_inert_denominator q 1 s hq norm_one hs
  rw [one_mul] at hn
  unfold inertFactor
  apply div_ne_zero
  · intro h; rw [h, norm_zero] at hn; linarith
  · intro h; rw [h, norm_zero] at hd; linarith
end Formalism.IrreducibleCountingLemmas.Z
