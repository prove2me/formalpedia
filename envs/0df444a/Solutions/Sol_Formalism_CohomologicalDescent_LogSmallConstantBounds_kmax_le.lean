-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LogSmallConstantBounds.kmax_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:29:54.461809+00:00
-- url     : https://prove2.me/submissions/257b587c-d1c7-4865-9aab-a318abafae99

import Definitions.Def_Formalism_PieriBlockIdeals_MertensReciprocalElementary
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SharperSizeNeedsMleKFalse
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LocalComponentGL
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LogarithmEquivalence
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_CardLargePrimeFactorsLeOneHolds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_b_div_lstar_pos

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
    (P.kmax : ℝ) ≤ 2 * (P.b / P.lstar) := by
  have hbl := b_div_lstar_pos H G
  have h0 : (0 : ℝ) ≤ 2 * P.b / P.lstar := by rw [mul_div_assoc]; linarith
  calc (P.kmax : ℝ) = ((⌊2 * P.b / P.lstar⌋₊ : ℕ) : ℝ) := rfl
    _ ≤ 2 * P.b / P.lstar := Nat.floor_le h0
    _ = 2 * (P.b / P.lstar) := by ring
end Formalism.CohomologicalDescent.LogSmallConstantBounds
