-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.rowPart_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:14:07.031802+00:00
-- url     : https://prove2.me/submissions/3674e0c6-8193-4279-9bf5-59aa4f9ec273

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
theorem _root_.solution {r n : ℕ} (k : ℕ) (m m' : Fin r × Fin n →₀ ℕ) :
    rowPart k (m + m') = rowPart k m + rowPart k m' := by
  simp [rowPart, rowDeg_add, Finset.sum_add_distrib]
end Formalism.GradedWeylDivisibility
