-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qn_pt_empty
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:45:42.505225+00:00
-- url     : https://prove2.me/submissions/185761eb-4cd4-4830-9c76-d39e672a18ff

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwlineLemmas
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QnPtEmpty
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
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
open Formalism.GradedWeylDivisibility
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (n : ℕ) (F : MvPolynomial (Fin n × Fin n) ℚ) :
    aeval (qn_pt n ∅) F = C (eval (idFrame ℚ n n) F) := by
  have h : (aeval (qn_pt n ∅)).toRingHom = (C : ℚ →+* MvPolynomial (Fin n × Fin n) ℚ).comp (eval (idFrame ℚ n n)) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [algebraMap_eq]
    · rintro ⟨b, c⟩
      by_cases hbc : b = c
      · subst hbc; simp [qn_pt, idFrame]
      · have : b.val ≠ c.val := fun h => hbc (Fin.ext h)
        simp [qn_pt, idFrame, hbc, this]
  exact congrArg (fun φ => φ F) h
end Formalism.InvariantFactorPaths.ColumnFamilies
