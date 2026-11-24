-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LogSmallConstantBounds.le_floor_h
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:47:05.022956+00:00
-- url     : https://prove2.me/submissions/528dccb4-8aad-4181-8856-0f933d2d8986

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
theorem _root_.solution {P : Par} (H : P.Hyp) {z : ℤ} (hz : (z : ℝ) ≤ P.h) :
    z ≤ ((⌊P.h⌋₊ : ℕ) : ℤ) := by
  rcases le_or_gt z 0 with hz0 | hz0
  · have : (0 : ℤ) ≤ ((⌊P.h⌋₊ : ℕ) : ℤ) := by positivity
    linarith
  · have e : ((z.toNat : ℕ) : ℝ) = (z : ℝ) := by
      have : ((z.toNat : ℕ) : ℤ) = z := Int.toNat_of_nonneg hz0.le
      exact_mod_cast this
    have h1 : z.toNat ≤ ⌊P.h⌋₊ := Nat.le_floor (by rw [e]; exact hz)
    omega
end Formalism.CohomologicalDescent.LogSmallConstantBounds
