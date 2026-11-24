-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LogSmallConstantBounds.mem_primesLe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:47:00.777646+00:00
-- url     : https://prove2.me/submissions/9c533d80-ac74-4998-830d-1bbefa4a063d

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
theorem _root_.solution {y : ℝ} (hy : 0 ≤ y) {p : ℕ} : p ∈ pr y ↔ p.Prime ∧ (p : ℝ) ≤ y := by
  unfold pr
  rw [Finset.mem_filter, Finset.mem_range, Nat.lt_add_one_iff, Nat.le_floor_iff hy]
  exact and_comm
end Formalism.CohomologicalDescent.LogSmallConstantBounds
