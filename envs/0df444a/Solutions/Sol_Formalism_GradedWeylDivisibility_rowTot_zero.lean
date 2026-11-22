-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.rowTot_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:15:10.531585+00:00
-- url     : https://prove2.me/submissions/90505f08-2015-47ff-a9a9-18f1a1e09447

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetdomLemmas
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDeg_zero

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
theorem _root_.solution {r n : ℕ} : rowTot (0 : Fin r × Fin n →₀ ℕ) = 0 := by
  simp [rowTot, rowDeg_zero]
end Formalism.GradedWeylDivisibility
