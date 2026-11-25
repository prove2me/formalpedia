-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LogSmallConstantBounds.exceptionalRange_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:07:58.64959+00:00
-- url     : https://prove2.me/submissions/ac2aea92-8408-4168-9fe6-34445cc0710a

import Definitions.Def_Formalism_PieriBlockIdeals_MertensReciprocalElementary
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SharperSizeNeedsMleKFalse
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LocalComponentGL
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LogarithmEquivalence
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_CardLargePrimeFactorsLeOneHolds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_lstar_pos
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_b_div_lstar_pos
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_two_mul_lstar_le_b
import Theorems.Thm_P2M_Formalism_CohomologicalDescent_LogSmallConstantBounds_eta_nonneg__1aa77f39dc77
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_kmax_le
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_paramsLJ_holds
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
private theorem size_bounds_of_large {P : Par} (H : P.Hyp) (G : P.Large) :
    P.S + P.η < P.lstar ∧ 2 * P.η + P.t + 8 * (P.b / P.lstar) + 7 < P.lstar ∧
      2 * P.lstar ≤ P.b ∧ 0 < P.b / P.lstar ∧ (P.kmax : ℝ) ≤ 2 * (P.b / P.lstar) ∧
      P.h = P.b + P.S + P.η + P.t + 1 ∧ 0 ≤ P.η ∧ (P.t : ℝ) ≤ P.η ∧ 0 ≤ P.S ∧ 0 < P.lstar := by
  have h1 := H.sum_lt
  have h2 := H.win_lt
  have hb' := H.b'_pos
  have hbl := b_div_lstar_pos H G
  have e : 8 * P.b / P.lstar = 8 * (P.b / P.lstar) := by ring
  exact ⟨by linarith, by linarith, two_mul_lstar_le_b H G, hbl, kmax_le H G, rfl, eta_nonneg' H,
    H.t_le, H.S_nonneg, lstar_pos H G⟩
end Formalism.CohomologicalDescent.LogSmallConstantBounds
end
end

set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LogSmallConstantBounds
open Classical
namespace Formalism.CohomologicalDescent.LogSmallConstantBounds
theorem _root_.solution : ExceptionalRange := by
  intro P H G z hz1 hz2
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := size_bounds_of_large H G
  have hLJ := paramsLJ_holds P H G
  have ht0 : (0 : ℝ) ≤ P.t := Nat.cast_nonneg _
  constructor
  · have : (0 : ℝ) < z := by linarith
    exact_mod_cast this
  · linarith [hLJ.2.2.2, hLJ.2.1]
end Formalism.CohomologicalDescent.LogSmallConstantBounds
