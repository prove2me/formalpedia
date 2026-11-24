-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.rowTot_single
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:29:04.496781+00:00
-- url     : https://prove2.me/submissions/13bc1599-068a-4a52-8a96-65d8eb29986d

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetdomLemmas
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDeg_single

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
theorem _root_.solution {r n : ℕ} (b : Fin r) (s : Fin n) :
    rowTot (Finsupp.single (b, s) 1 : Fin r × Fin n →₀ ℕ) = 1 := by
  classical
  unfold rowTot
  simp only [rowDeg_single]
  simp
end Formalism.GradedWeylDivisibility
