-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LogSmallConstantBounds.subset_primesLe_h_add_Nr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:04:56.475285+00:00
-- url     : https://prove2.me/submissions/c4c24db2-c453-45c4-b1ca-258b7075eaa4

import Definitions.Def_Formalism_PieriBlockIdeals_MertensReciprocalElementary
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SharperSizeNeedsMleKFalse
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LocalComponentGL
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LogarithmEquivalence
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_CardLargePrimeFactorsLeOneHolds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Theorems.Thm_P2M_Formalism_CohomologicalDescent_LogSmallConstantBounds_b_pos__c78f2de8288c
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_b_add_seven_le_h
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_subset_primesLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LogSmallConstantBounds
open Classical
namespace Formalism.CohomologicalDescent.LogSmallConstantBounds
theorem _root_.solution {P : Par} (H : P.Hyp) (G : P.Large) {R : Finset ℕ}
    (hR : ∀ l ∈ R, l.Prime ∧ P.lJ < (l : ℝ) ∧ (l : ℝ) ≤ P.h) : R ⊆ pr (P.h + (P.Nr : ℝ)) := by
  have hb := b_pos' P
  have h7 := b_add_seven_le_h H
  have hNr0 : (0 : ℝ) ≤ P.Nr := Nat.cast_nonneg _
  exact subset_primesLe (by linarith) (fun l hl => ⟨(hR l hl).1, by linarith [(hR l hl).2.2]⟩)
end Formalism.CohomologicalDescent.LogSmallConstantBounds
