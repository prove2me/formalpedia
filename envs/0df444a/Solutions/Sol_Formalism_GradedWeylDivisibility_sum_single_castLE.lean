-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.sum_single_castLE
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:30:35.613952+00:00
-- url     : https://prove2.me/submissions/6aca124f-01d9-4b94-98f3-9afde964263d

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetMinor

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
theorem _root_.solution {n s : ℕ} (hs : s ≤ n) :
    (∑ q : Fin s, (Pi.single (Fin.castLE hs q) 1 : Fin n → ℕ)) = initW n s := by
  funext t
  rw [Finset.sum_apply]
  simp only [initW]
  by_cases h : t.val < s
  · rw [if_pos h, Finset.sum_eq_single ⟨t.val, h⟩]
    · have e : Fin.castLE hs ⟨t.val, h⟩ = t := Fin.ext rfl
      rw [e, Pi.single_eq_same]
    · intro q _ hq
      rw [Pi.single_apply, if_neg]
      intro htq
      apply hq
      subst htq
      exact Fin.ext rfl
    · intro hq
      exact absurd (Finset.mem_univ _) hq
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun q _ => ?_
    rw [Pi.single_apply, if_neg]
    intro htq
    apply h
    subst htq
    exact q.isLt
end Formalism.GradedWeylDivisibility
