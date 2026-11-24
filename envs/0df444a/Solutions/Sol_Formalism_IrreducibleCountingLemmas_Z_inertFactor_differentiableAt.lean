-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.Z.inertFactor_differentiableAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:53:24.173987+00:00
-- url     : https://prove2.me/submissions/b2569cb8-fffc-4d31-9636-a5fccf75e8f8

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
    (hs : 1 / 2 < s.re) : DifferentiableAt ℂ (fun z => inertFactor q ch z) s := by
  have hc : ((q ^ 2 : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < q ^ 2 := by positivity
    exact_mod_cast this.ne'
  have hu : DifferentiableAt ℂ (fun z : ℂ => ((q ^ 2 : ℝ) : ℂ) ^ (-z)) s :=
    (differentiableAt_id.neg).const_cpow (Or.inl hc)
  unfold inertFactor
  refine ((differentiableAt_const _).sub hu).div
    ((differentiableAt_const _).sub ((differentiableAt_const _).mul hu)) ?_
  intro h
  have := half_le_norm_inert_denominator q ch s hq hch hs
  rw [h, norm_zero] at this
  linarith
end Formalism.IrreducibleCountingLemmas.Z
