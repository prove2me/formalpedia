-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qd_W_closed
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:10:42.471354+00:00
-- url     : https://prove2.me/submissions/40a825de-6191-4900-bad8-ff84e23ae41f

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_EqSmulCanonicalOfUnipotentInvariant
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcEvGLDetUZpow
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_TranslatesSpanCanonical
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_vander
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_eval_rowGen
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_det_E
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_mul
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowActMul
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
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
open Formalism.GradedWeylDivisibility
variable {n : ℕ}
variable [NeZero n]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (mu : Fin n → ℤ) : RowDivClosed (translatesSpanCanonical mu) := by
  intro a b k f hf
  have : translatesSpanCanonical mu ≤ (translatesSpanCanonical mu).comap (rowDivL ℚ a b k) := by
    unfold translatesSpanCanonical
    rw [Submodule.span_le]
    rintro _ ⟨g, hg, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, rowDivL_apply]
    apply qd_vander
    intro t
    rw [qd_eval_rowGen, ← AlgHom.comp_apply, rowActMul]
    apply Submodule.subset_span
    exact ⟨_, by rw [Matrix.det_mul]; exact hg.mul (qd_det_E a b t), rfl⟩
  exact this hf
end Formalism.InvariantFactorPaths.ColumnFamilies
