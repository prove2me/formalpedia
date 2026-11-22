-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.rowDeg_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:11:36.481093+00:00
-- url     : https://prove2.me/submissions/8c7ca27f-bd58-42fe-a72b-baddc72aa42d

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
theorem _root_.solution {r n : ℕ} (a : Fin r) : rowDeg (0 : Fin r × Fin n →₀ ℕ) a = 0 := by
  simp [rowDeg]
end Formalism.GradedWeylDivisibility
