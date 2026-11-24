-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LA.la_mono_of_weight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:53:10.393443+00:00
-- url     : https://prove2.me/submissions/b6944827-9591-4e66-866b-0b0cbc75ed68

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLA
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDlatLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_PadicValIntProdElevenMultiples
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_JointExactExponentStopHigh
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
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
noncomputable section
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LA
open Formalism.GradedWeylDivisibility
namespace Formalism.CohomologicalDescent.LA
theorem _root_.solution {m : Fin 2 × Fin 1 →₀ ℕ} {ν : Fin 1 → ℕ}
    (h : Finsupp.weight (colW 2 1) m = ν) :
    m = la_mono (0 : Fin 1) (m (0, 0)) (m (1, 0)) ∧ m (0, 0) + m (1, 0) = ν 0 := by
  have h0 := congrFun h 0
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)] at h0
  simp [Fintype.sum_prod_type, Fin.sum_univ_two, colW] at h0
  refine ⟨?_, h0⟩
  ext ⟨i, j⟩
  fin_cases i <;> fin_cases j <;> simp [la_mono, Finsupp.single_apply]
end Formalism.CohomologicalDescent.LA
