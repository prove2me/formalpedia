-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LogSmallConstantBounds.noWindowOf_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:26:30.673807+00:00
-- url     : https://prove2.me/submissions/71b238b4-ba76-413f-a91f-c942a3baf42d

import Definitions.Def_Formalism_PieriBlockIdeals_MertensReciprocalElementary
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SharperSizeNeedsMleKFalse
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LocalComponentGL
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LogarithmEquivalence
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_CardLargePrimeFactorsLeOneHolds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_noWindowResidue_holds

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
theorem _root_.solution : NoWindowOf := by
  intro P H G ι D pl l hl hlJ hEx τ
  have kind : ∀ e : ℝ, (P.Thick e ∨ P.Top e ∨ P.Thin e) →
      ((P.Thick e ∧ ¬ P.Excl l) ∨ P.Top e ∨ P.Thin e) := by
    intro e h
    rcases h with h | h | h
    · exact Or.inl ⟨h, hEx⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  constructor
  · rw [pl.mw_eq τ l]
    exact noWindowResidue_holds P H G l hl hlJ _ _ _ _ _ (pl.shape τ) (kind _ (pl.kind τ))
  · rw [pl.mwF_eq τ l]
    exact noWindowResidue_holds P H G l hl hlJ _ _ _ _ _ (pl.shapeF τ l) (kind _ (pl.kindF τ l))
end Formalism.CohomologicalDescent.LogSmallConstantBounds
