-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.rowPart_single
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:29:04.105322+00:00
-- url     : https://prove2.me/submissions/01b59673-8708-47a1-8bf6-29c5cc543b0d

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
theorem _root_.solution {r n : ℕ} (k : ℕ) (b : Fin r) (s : Fin n) :
    rowPart k (Finsupp.single (b, s) 1 : Fin r × Fin n →₀ ℕ) = if b.val < k then 1 else 0 := by
  classical
  unfold rowPart
  simp only [rowDeg_single]
  rw [Finset.sum_ite_eq]
  simp
end Formalism.GradedWeylDivisibility
