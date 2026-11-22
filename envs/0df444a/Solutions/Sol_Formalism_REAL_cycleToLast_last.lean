-- Prove2me | solution 1 for Formalism.REAL.cycleToLast_last
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:38:09.479219+00:00
-- url     : https://prove2.me/submissions/df9e5939-97e4-46fc-be3b-456bbb4f5301

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementE
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution (m : ℕ) (j : Fin (m + 1)) : cycleToLast m j (Fin.last m) = j := by
  simp only [cycleToLast, Equiv.trans_apply, Fin.revPerm_apply, Fin.rev_last, Fin.cycleRange_symm_zero, Fin.rev_rev]
end Formalism.REAL
