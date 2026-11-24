-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qd_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:27:22.508701+00:00
-- url     : https://prove2.me/submissions/b7dd4dd6-d0a6-4ab2-aac5-c755c4269ee1

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_EqSmulCanonicalOfUnipotentInvariant
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcEvGLDetUZpow
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_TranslatesSpanCanonical
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_W_eq
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_Lam_L
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_translate
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_ColumnFamilies_tableauBideterminant_mem_dualWeyl__7ff99547ec57


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
open Formalism.GradedWeylDivisibility
variable {n : ℕ}
variable [NeZero n]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (mu : Fin n → ℤ) (w : TIdx mu → ℚ) :
    ∃ w' ∈ Submodule.span ℚ (Set.range (qd_gcan mu)), qd_Lam mu w = qd_Lam mu w' := by
  have h1 : (∑ K, w K • qd_P mu K) ∈ translatesSpanCanonical mu := by
    rw [qd_W_eq]
    exact Submodule.sum_mem _ fun K _ => Submodule.smul_mem _ _ (tableauBideterminant_mem_dualWeyl' mu K)
  have h2 : translatesSpanCanonical mu ≤ (Submodule.span ℚ (Set.range (qd_gcan mu))).map
      (Fintype.linearCombination ℚ (fun K : TIdx mu => qd_P mu K)) := by
    unfold translatesSpanCanonical
    rw [Submodule.span_le]
    rintro _ ⟨g, hg, rfl⟩
    set γ : GL (Fin n) ℚ := Matrix.GeneralLinearGroup.mk'' g.transpose (by rwa [Matrix.det_transpose]) with hγ
    have hv : γ.val.transpose = g := by
      rw [hγ]; exact Matrix.transpose_transpose g
    refine ⟨(((Matrix.GeneralLinearGroup.det γ ^ mu (lastIdx n) : ℚˣ) : ℚ))⁻¹ • qd_gcan mu γ,
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨γ, rfl⟩), ?_⟩
    rw [map_smul, Fintype.linearCombination_apply, qd_translate, hv, smul_smul,
      inv_mul_cancel₀ (Units.ne_zero _), one_smul]
  obtain ⟨w', hw', he⟩ := h2 h1
  refine ⟨w', hw', ?_⟩
  rw [qd_Lam_L, qd_Lam_L, ← he, Fintype.linearCombination_apply]
end Formalism.InvariantFactorPaths.ColumnFamilies
