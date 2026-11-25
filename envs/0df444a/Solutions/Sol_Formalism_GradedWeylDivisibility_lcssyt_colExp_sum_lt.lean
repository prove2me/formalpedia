-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.lcssyt_colExp_sum_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:49:38.161492+00:00
-- url     : https://prove2.me/submissions/b20f20c0-fc36-466e-8c93-d991ed00ca86

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LCssytLemmas
import Theorems.Thm_Formalism_GradedWeylDivisibility_lcssyt_colExp_apply_lt

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
theorem _root_.solution {r n h : ℕ} (c : Fin h → Fin r) (hh : h ≤ n) (S : Finset (Fin r)) (t : Fin n)
    (ht : t.val < h) : ∑ b ∈ S, colExp c hh (b, t) = if c ⟨t.val, ht⟩ ∈ S then 1 else 0 := by
  simp only [lcssyt_colExp_apply_lt c hh _ t ht]
  exact Finset.sum_ite_eq S (c ⟨t.val, ht⟩) (fun _ => 1)
end Formalism.GradedWeylDivisibility
