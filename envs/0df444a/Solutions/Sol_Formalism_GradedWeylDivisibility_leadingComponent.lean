-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.leadingComponent
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:28:52.593483+00:00
-- url     : https://prove2.me/submissions/7c9119c0-f6bf-4382-a7c5-e1513b6235ec

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LeadComp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open scoped MonomialOrder
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution : LeadComp := by
  intro R _ r n M _ w f
  classical
  by_cases hf : f = 0
  · subst hf; simp
  have hd : (colLex r n).degree f ∈
      (weightedHomogeneousComponent w (Finsupp.weight w ((colLex r n).degree f)) f).support := by
    rw [mem_support_iff, coeff_weightedHomogeneousComponent, if_pos rfl]
    exact (colLex r n).coeff_degree_ne_zero_iff.mpr hf
  have hg0 : weightedHomogeneousComponent w (Finsupp.weight w ((colLex r n).degree f)) f ≠ 0 := by
    intro h; rw [h] at hd; simp at hd
  have h1 := (colLex r n).le_degree hd
  have h2 : (colLex r n).toSyn ((colLex r n).degree
      (weightedHomogeneousComponent w (Finsupp.weight w ((colLex r n).degree f)) f)) ≤
      (colLex r n).toSyn ((colLex r n).degree f) := by
    apply (colLex r n).le_degree
    have h3 := (colLex r n).degree_mem_support hg0
    rw [mem_support_iff, coeff_weightedHomogeneousComponent] at h3
    split_ifs at h3 with h
    · exact mem_support_iff.mpr h3
    · exact absurd rfl h3
  exact (colLex r n).toSyn.injective (le_antisymm h2 h1)
end Formalism.GradedWeylDivisibility
