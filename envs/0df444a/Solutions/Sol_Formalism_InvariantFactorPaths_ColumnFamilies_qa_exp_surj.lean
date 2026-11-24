-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qa_exp_surj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:10:11.542918+00:00
-- url     : https://prove2.me/submissions/9807fdca-a4fd-41a6-aadd-0871005aab6f

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QaRowStrictMono
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QaNuAntitone
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qa_fill_exists
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qa_fill_std
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qa_fill_exp

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
    (hm : m ∈ Formalism.GradedWeylDivisibility.ssIdx n n (qa_nu mu)) : ∃ I : TIdx mu, StdT I ∧ qa_exp I = m := by
  obtain ⟨I, hI⟩ := qa_fill_exists hmu m hm.1 hm.2
  exact ⟨I, qa_fill_std hmu m hm.2 I hI, qa_fill_exp hmu m hm.2 I hI⟩
end Formalism.InvariantFactorPaths.ColumnFamilies
