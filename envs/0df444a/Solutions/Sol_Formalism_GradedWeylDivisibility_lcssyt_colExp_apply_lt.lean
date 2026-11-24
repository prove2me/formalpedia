-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.lcssyt_colExp_apply_lt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:14:45.877918+00:00
-- url     : https://prove2.me/submissions/63b9c4ea-2247-4ec3-890f-7eb093242ee5

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LCssytLemmas

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Finset
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution {r n h : ℕ} (c : Fin h → Fin r) (hh : h ≤ n) (a : Fin r) (t : Fin n)
    (ht : t.val < h) : colExp c hh (a, t) = if c ⟨t.val, ht⟩ = a then 1 else 0 := by
  unfold colExp
  rw [Finsupp.finset_sum_apply, Finset.sum_eq_single ⟨t.val, ht⟩]
  · rw [Finsupp.single_apply]
    congr 1
    apply propext
    constructor
    · intro he; exact (Prod.ext_iff.mp he).1
    · intro he; exact Prod.ext he (Fin.ext rfl)
  · intro p _ hp
    rw [Finsupp.single_apply, if_neg]
    intro he
    apply hp
    have := congrArg (fun x => x.2.val) he
    exact Fin.ext (by simpa using this)
  · simp
end Formalism.GradedWeylDivisibility
