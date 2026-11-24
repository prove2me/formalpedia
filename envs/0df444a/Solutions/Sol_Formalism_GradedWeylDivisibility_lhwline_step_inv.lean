-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.lhwline_step_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:05:18.43952+00:00
-- url     : https://prove2.me/submissions/52016740-328b-472c-b06c-43582644ac30

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementB
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwrowLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwlineLemmas
import Theorems.Thm_Formalism_GradedWeylDivisibility_lhwline_mrow_inv
import Theorems.Thm_Formalism_GradedWeylDivisibility_lhwline_mcol_inv
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
open Formalism Formalism.GradedWeylDivisibility
variable {K : Type*} [Field K] {r n : ℕ}
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution (φ : (Fin r × Fin n → K) → K) (hR : lhwline_RInv φ) (hC : lhwline_CInv φ)
    (p : Fin r) (q : Fin n) (x : Fin r × Fin n → K) : φ (highestWeightLineUpdate p q x) = φ x := by
  simp only [highestWeightLineUpdate]
  exact (lhwline_mcol_inv φ hC q _ _ _ (fun j hj => (Finset.mem_filter.1 hj).2)).trans
    (lhwline_mrow_inv φ hR p _ x _ (fun b hb => (Finset.mem_filter.1 hb).2))
end Formalism.GradedWeylDivisibility
