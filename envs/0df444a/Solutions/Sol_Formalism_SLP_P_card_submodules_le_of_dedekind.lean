-- Prove2me | solution 1 for Formalism.SLP.P.card_submodules_le_of_dedekind
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:37:21.910443+00:00
-- url     : https://prove2.me/submissions/39cc88f9-f6e0-488d-a629-ba2eea655afb

import Definitions.Def_Formalism_HyperbolicPlaceProducts_Statement
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_DedekindLFunctions
import Theorems.Thm_Formalism_SLP_P_exists_family_span_eq_of_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
noncomputable section
open Formalism Formalism.SLP Formalism.SLP.P
namespace Formalism.SLP.P
theorem _root_.solution : Formalism.SLP.SubmoduleCountDed := by
  intro R M _ _ _ _ _ e v hv
  have hsurj : Function.Surjective
      (fun t : Fin e → M => Submodule.span R (Set.range t)) := by
    intro N
    exact exists_family_span_eq_of_le e v N (by rw [hv]; exact le_top)
  calc Nat.card (Submodule R M) ≤ Nat.card (Fin e → M) :=
        Nat.card_le_card_of_surjective _ hsurj
    _ = Nat.card M ^ e := by
        rw [Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
end Formalism.SLP.P
