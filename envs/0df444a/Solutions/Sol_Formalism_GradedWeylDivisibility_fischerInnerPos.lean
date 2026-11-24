-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.fischerInnerPos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:01:14.466782+00:00
-- url     : https://prove2.me/submissions/feabfe1b-bdf7-4298-b54c-e78694267b58

import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFockbLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockPos
import Theorems.Thm_Formalism_GradedWeylDivisibility_LFockb_fockF_self


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution : FockPos := by
  intro σ f hf
  rw [LFockb_fockF_self]
  refine ⟨?_, Complex.ofReal_im _⟩
  rw [Complex.ofReal_re]
  apply Finset.sum_pos
  · intro m hm
    apply mul_pos
    · exact Complex.normSq_pos.mpr (mem_support_iff.mp hm)
    · exact Nat.cast_pos.mpr (Finset.prod_pos fun k _ => Nat.factorial_pos _)
  · exact Finset.nonempty_of_ne_empty fun h => hf (support_eq_empty.mp h)
end Formalism.GradedWeylDivisibility
