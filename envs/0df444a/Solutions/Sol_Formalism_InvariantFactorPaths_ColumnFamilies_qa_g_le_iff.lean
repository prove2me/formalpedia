-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qa_g_le_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:32:41.847482+00:00
-- url     : https://prove2.me/submissions/b5b2ae01-7ff3-4b45-8e26-cb012dcbfcfa

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QaRowStrictMono
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QaNuAntitone
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qa_S_mono
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qa_S_last
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qa_lower_iff
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
theorem _root_.solution {n : ℕ} [NeZero n] (m : Fin n × Fin n →₀ ℕ) (k : ℤ) (p : Fin n)
    (hk : k ≤ (∑ b : Fin n, m (b, p) : ℕ)) (a : Fin n) : qa_g m k p ≤ a ↔ k ≤ qa_S m a p := by
  have hl := qa_lower_iff (fun a : Fin n => (qa_S m a p : ℤ) < k)
    (fun q q' hqq hq => lt_of_le_of_lt (by exact_mod_cast qa_S_mono m p hqq) hq)
  have hn : (univ.filter fun a : Fin n => (qa_S m a p : ℤ) < k).card < n := by
    have h1 := hl (lastIdx n)
    rw [qa_S_last] at h1
    have h2 : ¬ (lastIdx n).val < (univ.filter fun a : Fin n => (qa_S m a p : ℤ) < k).card :=
      fun hh => absurd (h1.mpr hh) (not_lt.mpr hk)
    have h3 : (lastIdx n).val = n - 1 := rfl
    have := NeZero.pos n
    omega
  unfold qa_g
  rw [dif_pos hn, Fin.le_def]
  have h1 := hl a
  constructor
  · intro h
    by_contra hc
    have := h1.mp (not_le.mp hc)
    simp only at h
    omega
  · intro h
    by_contra hc
    have := h1.mpr (not_le.mp hc)
    omega
end Formalism.InvariantFactorPaths.ColumnFamilies
