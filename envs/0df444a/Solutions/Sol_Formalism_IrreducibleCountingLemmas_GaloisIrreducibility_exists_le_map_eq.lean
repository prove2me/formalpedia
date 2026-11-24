-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.exists_le_map_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:06:10.855834+00:00
-- url     : https://prove2.me/submissions/9df7dca7-bf59-46e4-8ddc-c628cda3ce6a

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisIrreducibility
import Definitions.Def_Lemmata_GeneralBFactRightRest_Imports
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRDivisorDegreeSubSum
import Theorems.Thm_Bl_general_b_fact_right_rest_goal1


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial UniqueFactorizationMonoid
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
open Formalism.GaloisIrreducibility (IsSubSum)
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution {α β : Type*} [DecidableEq β] (f : α → β) (t : Multiset α) :
    ∀ s : Multiset β, s ≤ t.map f → ∃ u ≤ t, u.map f = s := by
  first | exact Bl.general_b_fact_right_rest.goal1 .. | (apply Bl.general_b_fact_right_rest.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_right_rest.goal1 <;> assumption) | (apply @Bl.general_b_fact_right_rest.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_right_rest.goal1 <;> assumption) | (apply @Bl.general_b_fact_right_rest.goal1 <;> first | assumption | infer_instance) | exact @Bl.general_b_fact_right_rest.goal1 α β ‹_› f t s ‹_› | exact @Bl.general_b_fact_right_rest.goal1 α β ‹_› f t s | exact @Bl.general_b_fact_right_rest.goal1 α β ‹_› f t | exact @Bl.general_b_fact_right_rest.goal1 α β ‹_› f | exact @Bl.general_b_fact_right_rest.goal1 α β ‹_› | exact @Bl.general_b_fact_right_rest.goal1 α β | exact @Bl.general_b_fact_right_rest.goal1 α
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
