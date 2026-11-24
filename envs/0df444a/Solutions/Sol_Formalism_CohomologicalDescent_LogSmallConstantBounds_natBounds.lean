-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LogSmallConstantBounds.natBounds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:46:52.358692+00:00
-- url     : https://prove2.me/submissions/27c52067-283f-4836-99b9-9cfe548bb4a1

import Definitions.Def_Formalism_PieriBlockIdeals_MertensReciprocalElementary
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SharperSizeNeedsMleKFalse
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LocalComponentGL
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LogarithmEquivalence
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_CardLargePrimeFactorsLeOneHolds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds

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
theorem _root_.solution {P : Par} (H : P.Hyp) : NatBounds P := by
  have hm : (1 : ℝ) ≤ P.m := by exact_mod_cast H.m_pos
  have hk : (1 : ℝ) ≤ P.k := by exact_mod_cast le_trans H.m_pos H.m_le
  have ht : (P.k : ℝ) + P.m + 4 ≤ P.t := by exact_mod_cast H.t_ge
  have hN : (P.Nr : ℝ) + 1 = P.k + P.m + P.t := by exact_mod_cast H.Nr_eq
  exact ⟨hm, by exact_mod_cast H.n_pos, by exact_mod_cast H.f_pos, hk,
    by exact_mod_cast H.m_le, ht, by exact_mod_cast H.t_gt, by linarith, hN, by linarith⟩
end Formalism.CohomologicalDescent.LogSmallConstantBounds
