-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.lhwline_elim_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:10:22.519796+00:00
-- url     : https://prove2.me/submissions/bd69ac38-49b0-4649-b031-e4fa16913f9f

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementB
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwrowLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwlineLemmas
import Theorems.Thm_Formalism_GradedWeylDivisibility_lhwline_step_inv
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
    (k : ℕ) (x : Fin r × Fin n → K) : φ (lhwline_elim k x) = φ x := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [lhwline_elim]
    split_ifs with h
    · rw [lhwline_step_inv φ hR hC, ih]
    · exact ih
end Formalism.GradedWeylDivisibility
