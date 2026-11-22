-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.rowPart_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:15:08.109599+00:00
-- url     : https://prove2.me/submissions/225b17fe-506a-451b-9083-0cd3fb51fafd

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
theorem _root_.solution {r n : ℕ} (k : ℕ) : rowPart k (0 : Fin r × Fin n →₀ ℕ) = 0 := by
  simp [rowPart, rowDeg_zero]
end Formalism.GradedWeylDivisibility
