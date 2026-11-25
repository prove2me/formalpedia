-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.StandardLattice.vandermondeAppendNeg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:18:32.542389+00:00
-- url     : https://prove2.me/submissions/75edf2a6-d33d-4621-8ff8-190bfa312406

import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeVariationUnbounded
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_BlockDimensionIdentities
import Theorems.Thm_P2M_Formalism_LogVandermondeBounds_StandardLattice_castAdd_lt_castAdd_iff__4f24d2149f8c
import Theorems.Thm_P2M_Formalism_LogVandermondeBounds_StandardLattice_castAdd_lt_natAdd__3ab05cecd610
import Theorems.Thm_P2M_Formalism_LogVandermondeBounds_StandardLattice_not_natAdd_lt_castAdd__c751723af974
import Theorems.Thm_P2M_Formalism_LogVandermondeBounds_StandardLattice_natAdd_lt_natAdd_iff__07d1b29b564b

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LogVandermondeBounds Formalism.LogVandermondeBounds.StandardLattice
open Finset
namespace Formalism.LogVandermondeBounds.StandardLattice
theorem _root_.solution : VandermondeAppendNeg := by
  intro R _ a m v b
  simp only [Finset.prod_filter]
  rw [Fin.prod_univ_add]
  simp only [Fin.prod_univ_add, Fin.append_left, Fin.append_right, castAdd_lt_castAdd_iff',
    castAdd_lt_natAdd', not_natAdd_lt_castAdd', natAdd_lt_natAdd_iff', if_true, if_false,
    Finset.prod_const_one, mul_one, one_mul, sub_neg_eq_add, neg_sub_neg, neg_add_eq_sub, Finset.prod_mul_distrib]
  ring
end Formalism.LogVandermondeBounds.StandardLattice
