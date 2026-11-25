-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.lcssyt_colExp_sum_ge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:49:32.523819+00:00
-- url     : https://prove2.me/submissions/7b180049-06be-4b40-8ae9-4a24902ca528

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LCssytLemmas
import Theorems.Thm_Formalism_GradedWeylDivisibility_lcssyt_colExp_apply_ge

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
    (ht : ¬ t.val < h) : ∑ b ∈ S, colExp c hh (b, t) = 0 := by
  simp [lcssyt_colExp_apply_ge c hh _ t ht]
end Formalism.GradedWeylDivisibility
