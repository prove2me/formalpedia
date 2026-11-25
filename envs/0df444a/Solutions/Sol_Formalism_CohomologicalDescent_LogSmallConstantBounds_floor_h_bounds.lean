-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LogSmallConstantBounds.floor_h_bounds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:08:05.65946+00:00
-- url     : https://prove2.me/submissions/d897bbae-4449-4c7e-9c10-ad89dbc50feb

import Definitions.Def_Formalism_PieriBlockIdeals_MertensReciprocalElementary
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SharperSizeNeedsMleKFalse
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LocalComponentGL
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LogarithmEquivalence
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_CardLargePrimeFactorsLeOneHolds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Theorems.Thm_P2M_Formalism_CohomologicalDescent_LogSmallConstantBounds_b_pos__c78f2de8288c
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_paramsBasic_holds
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_b_add_seven_le_h
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_paramsLJ_holds

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
theorem _root_.solution {P : Par} (H : P.Hyp) (G : P.Large) :
    (1 : ℝ) ≤ (⌊P.h⌋₊ : ℝ) ∧ (⌊P.h⌋₊ : ℝ) ≤ P.h ∧ (⌊P.h⌋₊ : ℝ) < P.lJ ^ 2 ∧
      0 ≤ Real.log (⌊P.h⌋₊ : ℝ) ∧ Real.log (⌊P.h⌋₊ : ℝ) ≤ Real.log P.h := by
  have hb := b_pos' P
  have h7 := b_add_seven_le_h H
  have hh := (paramsBasic_holds P H G).2.2
  have hLJ := paramsLJ_holds P H G
  have hh0 : 0 ≤ P.h := by linarith
  have f1 : (1 : ℝ) ≤ (⌊P.h⌋₊ : ℝ) := by
    have : 1 ≤ ⌊P.h⌋₊ := Nat.le_floor (by rw [Nat.cast_one]; linarith)
    exact_mod_cast this
  have f2 : (⌊P.h⌋₊ : ℝ) ≤ P.h := Nat.floor_le hh0
  exact ⟨f1, f2, by linarith [hLJ.2.1], Real.log_nonneg f1, Real.log_le_log (by linarith) f2⟩
end Formalism.CohomologicalDescent.LogSmallConstantBounds
