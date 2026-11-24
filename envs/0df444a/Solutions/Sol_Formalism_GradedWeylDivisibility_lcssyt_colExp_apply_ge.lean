-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.lcssyt_colExp_apply_ge
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:16:51.171428+00:00
-- url     : https://prove2.me/submissions/737a1da7-4146-4d23-8cff-071dda2d5958

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
    (ht : ¬ t.val < h) : colExp c hh (a, t) = 0 := by
  unfold colExp
  rw [Finsupp.finset_sum_apply]
  refine Finset.sum_eq_zero fun p _ => ?_
  rw [Finsupp.single_apply, if_neg]
  intro he
  apply ht
  have := congrArg (fun x => x.2.val) he
  simp only [Fin.coe_castLE] at this
  omega
end Formalism.GradedWeylDivisibility
