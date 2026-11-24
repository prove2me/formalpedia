-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.StandardLattice.zetaR_nonneg_le_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:53:05.132846+00:00
-- url     : https://prove2.me/submissions/652db2d9-aa3f-44af-a4e1-0eb07ed56902

import Definitions.Def_Formalism_LogVandermondeBounds_VandPlace
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_LogRatioLowerBoundOfLogVandermondeGap
import Theorems.Thm_Formalism_LogVandermondeBounds_StandardLattice_hasSum_inv_succ_sq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LogVandermondeBounds Formalism.LogVandermondeBounds.StandardLattice
open Finset
namespace Formalism.LogVandermondeBounds.StandardLattice
theorem _root_.solution (M : ℕ) (hM : 2 ≤ M) : 0 ≤ zetaR M ∧ zetaR M ≤ 2 := by
  have hle : ∀ n : ℕ, 1 / ((n : ℝ) + 1) ^ M ≤ 1 / ((n : ℝ) + 1) ^ 2 := by
    intro n
    have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
    apply one_div_le_one_div_of_le (by positivity)
    exact pow_le_pow_right₀ h1 hM
  have hnn : ∀ n : ℕ, 0 ≤ 1 / ((n : ℝ) + 1) ^ M := fun n => by positivity
  have hs : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ M) :=
    Summable.of_nonneg_of_le hnn hle hasSum_inv_succ_sq.summable
  refine ⟨tsum_nonneg hnn, ?_⟩
  have h3 : zetaR M ≤ Real.pi ^ 2 / 6 := hasSum_le hle hs.hasSum hasSum_inv_succ_sq
  have hp := Real.pi_lt_d2
  have hp0 := Real.pi_pos
  nlinarith
end Formalism.LogVandermondeBounds.StandardLattice
