-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.Z.inert_euler_quotient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:07:35.641229+00:00
-- url     : https://prove2.me/submissions/73f2e2bc-dbd4-4ea7-9003-da66cdad77b7

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_FactorOverLocalSubalgebraMonic
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZReuse
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZCircleCharExtends
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_FactorOverLocalSubalgebra
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_CharpolyFactorAnnihilator
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZGoodCuspidal
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZBrauerNesbitt
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_CardLtAddCardGtAddCardEq
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_Z_inertFactor_sub_one_le
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_Z_inertFactor_ne_zero
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_Z_BN_Kills_mul_left


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
theorem _root_.solution : InertEulerQuotient := by
  intro ι q ch s hq hch hs hsum
  have hS : Summable (fun v => ‖inertFactor (q v) (ch v) s - 1‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun v => inertFactor_sub_one_le (q v) (ch v) s (hq v) (hch v) hs) (hsum.mul_left 4)
  have e : (fun v => inertFactor (q v) (ch v) s) =
      fun v => 1 + (inertFactor (q v) (ch v) s - 1) := by
    funext v; ring
  refine ⟨hS, ?_, ?_⟩
  · rw [e]; exact multipliable_one_add_of_summable hS
  · rw [e]
    refine tprod_one_add_ne_zero_of_summable (fun v => ?_) hS
    rw [add_sub_cancel]
    exact inertFactor_ne_zero (q v) (ch v) s (hq v) (hch v) hs
end Formalism.IrreducibleCountingLemmas.Z
