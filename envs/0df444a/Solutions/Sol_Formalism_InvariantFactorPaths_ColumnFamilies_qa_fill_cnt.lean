-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qa_fill_cnt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:40:57.960524+00:00
-- url     : https://prove2.me/submissions/2b9171c7-51de-4019-9eb9-540ff62f1be1

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QaRowStrictMono
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QaNuAntitone
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qa_S_le
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qa_g_le_iff
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qa_nu_cast
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qa_cnt_le
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qa_lt_colH
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qa_row_le_iff


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
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (hmu : Dominant mu) (m : Fin n × Fin n →₀ ℕ)
    (hcol : ∀ t, ∑ a : Fin n, m (a, t) = qa_nu mu t) (I : TIdx mu)
    (hI : ∀ c q, qa_row I c q = qa_g m ((c : ℤ) - mu (lastIdx n)) (Fin.castLE (colH_le mu c) q))
    (c : ↥(TCols mu)) (a p : Fin n) :
    p.val < qa_cnt I c a ↔ (c : ℤ) - mu (lastIdx n) ≤ qa_S m a p := by
  have hc := Finset.mem_Ioc.mp c.2
  have key : ∀ hp : p.val < colH mu c, (p.val < qa_cnt I c a ↔ (c : ℤ) - mu (lastIdx n) ≤ qa_S m a p) := by
    intro hp
    have h1 := qa_row_le_iff I c ⟨p.val, hp⟩ a
    rw [hI] at h1
    have h2 : Fin.castLE (colH_le mu c) ⟨p.val, hp⟩ = p := Fin.ext rfl
    rw [h2, qa_g_le_iff] at h1
    · exact h1.symm
    · rw [hcol, qa_nu_cast hmu]
      have := (qa_lt_colH hmu c p).mp hp
      omega
  constructor
  · intro h
    exact (key (h.trans_le (qa_cnt_le I c a))).mp h
  · intro h
    have h1 := qa_S_le m a p
    rw [hcol] at h1
    have h2 := qa_nu_cast hmu p
    have hp : p.val < colH mu c := (qa_lt_colH hmu c p).mpr (by omega)
    exact (key hp).mpr h
end Formalism.InvariantFactorPaths.ColumnFamilies
