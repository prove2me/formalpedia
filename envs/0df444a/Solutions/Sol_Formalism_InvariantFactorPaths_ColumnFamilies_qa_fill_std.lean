-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qa_fill_std
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:45:14.791188+00:00
-- url     : https://prove2.me/submissions/79f03d4d-1ccc-448d-b473-199593e38a11

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QaRowStrictMono
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QaNuAntitone
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qa_fill_cnt
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qa_cnt_le
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
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (hmu : Dominant mu) (m : Fin n × Fin n →₀ ℕ)
    (hcol : ∀ t, ∑ a : Fin n, m (a, t) = qa_nu mu t) (I : TIdx mu)
    (hI : ∀ c q, qa_row I c q = qa_g m ((c : ℤ) - mu (lastIdx n)) (Fin.castLE (colH_le mu c) q)) : StdT I := by
  intro c hc a
  change qa_cnt I ⟨(c : ℤ) + 1, hc⟩ a ≤ qa_cnt I c a
  by_contra hlt
  have hlt := not_le.mp hlt
  have hn : qa_cnt I c a < n := hlt.trans_le ((qa_cnt_le I _ a).trans (colH_le mu _))
  have h1 := (qa_fill_cnt hmu m hcol I hI ⟨(c : ℤ) + 1, hc⟩ a ⟨qa_cnt I c a, hn⟩).mp hlt
  have h2 := (qa_fill_cnt hmu m hcol I hI c a ⟨qa_cnt I c a, hn⟩).mpr (by simp only at h1; omega)
  exact lt_irrefl _ h2
end Formalism.InvariantFactorPaths.ColumnFamilies
