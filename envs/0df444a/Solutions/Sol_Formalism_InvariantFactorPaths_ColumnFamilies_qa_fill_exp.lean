-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qa_fill_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:45:13.324888+00:00
-- url     : https://prove2.me/submissions/be859195-30f5-48e5-9ca2-dd5c2323182f

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QaRowStrictMono
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QaNuAntitone
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qa_S_le
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qa_of_cum
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qa_nu_cast
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qa_fill_cnt
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qa_card_sub
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qa_cum
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
    (hI : ∀ c q, qa_row I c q = qa_g m ((c : ℤ) - mu (lastIdx n)) (Fin.castLE (colH_le mu c) q)) :
    qa_exp I = m := by
  classical
  apply qa_of_cum
  intro a p
  change ∑ b : Fin n with b ≤ a, qa_exp I (b, p) = qa_S m a p
  rw [qa_cum, qa_card_sub]
  have h1 := qa_S_le m a p
  rw [hcol] at h1
  have h2 := qa_nu_cast hmu p
  have h3 : mu p ≤ mu 0 := hmu (Fin.zero_le p)
  have : ((TCols mu).filter fun d => ∃ h : d ∈ TCols mu, p.val < qa_cnt I ⟨d, h⟩ a) =
      Finset.Ioc (mu (lastIdx n)) (mu (lastIdx n) + qa_S m a p) := by
    ext d
    simp only [mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨hd, h, hp⟩
      have := (qa_fill_cnt hmu m hcol I hI ⟨d, h⟩ a p).mp hp
      have hd' := Finset.mem_Ioc.mp hd
      simp only at this
      omega
    · rintro ⟨hd1, hd2⟩
      have hd : d ∈ TCols mu := Finset.mem_Ioc.mpr ⟨hd1, by omega⟩
      exact ⟨hd, hd, (qa_fill_cnt hmu m hcol I hI ⟨d, hd⟩ a p).mpr (by simp only; omega)⟩
  rw [this, Int.card_Ioc]
  simp
end Formalism.InvariantFactorPaths.ColumnFamilies
