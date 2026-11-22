-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.rowDeg_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:11:26.928801+00:00
-- url     : https://prove2.me/submissions/d24bd206-4ef4-447f-b356-d43b1a3f3df7

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetdomLemmas

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
theorem _root_.solution {r n : ℕ} (m m' : Fin r × Fin n →₀ ℕ) (a : Fin r) :
    rowDeg (m + m') a = rowDeg m a + rowDeg m' a := by
  simp [rowDeg, Finset.sum_add_distrib]
end Formalism.GradedWeylDivisibility
