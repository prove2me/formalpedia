-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.lhwin_weight_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:21:19.537811+00:00
-- url     : https://prove2.me/submissions/6a90c153-aa2b-493b-bb60-a24c9b601585

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementB
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwinLemmas
import Theorems.Thm_Formalism_GradedWeylDivisibility_lhwin_weight_ht

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
theorem _root_.solution {r n : ℕ} (d : Fin r × Fin n →₀ ℕ) :
    0 ≤ Finsupp.weight (lhwinHt r n) d := by
  rw [lhwin_weight_ht]
  exact Finset.sum_nonneg fun a _ => by positivity
end Formalism.GradedWeylDivisibility
