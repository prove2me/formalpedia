-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.shape_complement_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:08:41.635804+00:00
-- url     : https://prove2.me/submissions/212b8b6e-6d37-4fd4-a8cb-a2c8c2e920c0

import Definitions.Def_Formalism_PieriBlockIdeals_LastGradedOfGradedAlone
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightShiftEqDetMul
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD
open Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LA
namespace Formalism.CohomologicalDescent.LD
theorem _root_.solution {r K : ℕ} (sz : Fin K → ℕ) (t : Fin r) :
    (∑ k, initW r (r - sz k)) t + shapeDeg sz (Fin.rev t) = K := by
  unfold shapeDeg
  rw [Finset.sum_apply, Finset.card_filter, ← Finset.sum_add_distrib]
  have h : ∀ k : Fin K, initW r (r - sz k) t + (if (Fin.rev t).val < sz k then 1 else 0) = 1 := by
    intro k
    have := t.isLt
    unfold initW
    rw [Fin.val_rev]
    split_ifs <;> omega
  rw [Finset.sum_congr rfl fun k _ => h k]
  simp
end Formalism.CohomologicalDescent.LD
