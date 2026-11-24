-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LogSmallConstantBounds.sum_one_add_log_div_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:14:35.916177+00:00
-- url     : https://prove2.me/submissions/9e95d97f-05fb-420c-9860-0759ddb42ade

import Definitions.Def_Formalism_PieriBlockIdeals_MertensReciprocalElementary
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SharperSizeNeedsMleKFalse
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LocalComponentGL
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LogarithmEquivalence
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_CardLargePrimeFactorsLeOneHolds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_log_div_prime_nonneg

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
theorem _root_.solution {P : Par} {R : Finset ℕ}
    (hR : ∀ l ∈ R, l.Prime ∧ P.lJ < (l : ℝ) ∧ (l : ℝ) ≤ P.h) (B : ℝ) (hB : 0 ≤ B)
    (hBl : ∀ l ∈ R, Real.log (P.h / (l : ℝ)) ≤ B) :
    ∑ l ∈ R, (1 + max 0 (Real.log (P.h / (l : ℝ)))) * (Real.log (l : ℝ) / (l : ℝ)) ≤
      (1 + B) * ∑ l ∈ R, Real.log (l : ℝ) / (l : ℝ) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro l hl
  have hmax : max 0 (Real.log (P.h / (l : ℝ))) ≤ B := max_le hB (hBl l hl)
  exact mul_le_mul_of_nonneg_right (by linarith) (log_div_prime_nonneg (hR l hl).1)
end Formalism.CohomologicalDescent.LogSmallConstantBounds
