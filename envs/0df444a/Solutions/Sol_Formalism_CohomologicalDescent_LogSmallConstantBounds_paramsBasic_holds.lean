-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LogSmallConstantBounds.paramsBasic_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:29:55.087569+00:00
-- url     : https://prove2.me/submissions/3f3b338b-dbf6-4699-8dfa-c5e78054689e

import Definitions.Def_Formalism_PieriBlockIdeals_MertensReciprocalElementary
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SharperSizeNeedsMleKFalse
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LocalComponentGL
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LogarithmEquivalence
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_CardLargePrimeFactorsLeOneHolds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_b_div_lstar_pos
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_two_mul_lstar_le_b
import Theorems.Thm_P2M_Formalism_CohomologicalDescent_LogSmallConstantBounds_eta_nonneg__1aa77f39dc77
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Finset
namespace Formalism.CohomologicalDescent.LogSmallConstantBounds
open Classical
private theorem lstar_bounds_of_large {P : Par} (H : P.Hyp) (G : P.Large) :
    P.S + P.η < P.lstar ∧ 2 * P.η + P.t + 7 < P.lstar ∧ 2 * P.lstar ≤ P.b ∧ 0 < P.b / P.lstar := by
  have h1 := H.sum_lt
  have h2 := H.win_lt
  have hb' := H.b'_pos
  have hbl := b_div_lstar_pos H G
  have e : 8 * P.b / P.lstar = 8 * (P.b / P.lstar) := by ring
  exact ⟨by linarith, by linarith, two_mul_lstar_le_b H G, hbl⟩
end Formalism.CohomologicalDescent.LogSmallConstantBounds
end
end

set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LogSmallConstantBounds
open Classical
namespace Formalism.CohomologicalDescent.LogSmallConstantBounds
theorem _root_.solution : Elem0 := by
  intro P H G
  have hNr := H.Nr_eq
  have htg := H.t_ge
  obtain ⟨a1, a2, a3, a4⟩ := lstar_bounds_of_large H G
  have hη := eta_nonneg' H
  have htη := H.t_le
  refine ⟨by omega, a3, ?_⟩
  unfold Formalism.CohomologicalDescent.LogSmallConstantBounds.Par.h
  linarith
end Formalism.CohomologicalDescent.LogSmallConstantBounds
