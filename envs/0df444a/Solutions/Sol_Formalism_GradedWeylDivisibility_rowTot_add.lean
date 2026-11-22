-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.rowTot_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:14:18.078814+00:00
-- url     : https://prove2.me/submissions/71c3045c-3ec6-47ae-8858-66d032402090

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetdomLemmas
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDeg_add

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
theorem _root_.solution {r n : ℕ} (m m' : Fin r × Fin n →₀ ℕ) :
    rowTot (m + m') = rowTot m + rowTot m' := by
  simp [rowTot, rowDeg_add, Finset.sum_add_distrib]
end Formalism.GradedWeylDivisibility
