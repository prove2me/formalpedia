-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qa_std_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:43:48.564113+00:00
-- url     : https://prove2.me/submissions/aeef2d1d-b4c1-477f-9592-65afef188938

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DefsMod
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementD
import Definitions.Def_Lemmata_GeneralBFactSecondTer_Imports
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QaRowStrictMono
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qa_seg
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qa_cum
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qa_card_sub

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
theorem _root_.solution {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (I : TIdx mu) (hI : StdT I) (c : ↥(TCols mu))
    (a p : Fin n) :
    p.val < qa_cnt I c a ↔
      (c : ℤ) - mu (lastIdx n) ≤ ((∑ b : Fin n with b ≤ a, qa_exp I (b, p) : ℕ) : ℤ) := by
  classical
  rw [qa_cum, qa_card_sub]
  have := qa_seg (mu (lastIdx n)) (mu 0) (fun d => ∃ h : d ∈ TCols mu, p.val < qa_cnt I ⟨d, h⟩ a) ?_ c c.2
  · rw [← TCols] at this
    rw [← this]
    exact ⟨fun h => ⟨c.2, h⟩, fun ⟨_, h⟩ => h⟩
  · rintro d hd hU ⟨h, hp⟩
    have hd' : d ∈ TCols mu := Finset.mem_Ioc.mpr ⟨hd, by omega⟩
    exact ⟨hd', hp.trans_le (hI ⟨d, hd'⟩ h a)⟩
end Formalism.InvariantFactorPaths.ColumnFamilies
