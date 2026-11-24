-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.StandardLattice.zetaR_le_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:37:42.053797+00:00
-- url     : https://prove2.me/submissions/674598e7-bcd9-475e-9036-e2444a2965a7

import Definitions.Def_Formalism_LogVandermondeBounds_UpperPlace
import Mathlib
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_LogRatioUpperBoundOfUpperPlace

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
theorem _root_.solution {M : ℕ} (hM : 2 ≤ M) : zetaR M ≤ 2 := by
  have hs2 : HasSum (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1) ^ 2) (Real.pi ^ 2 / 6) := by
    have := (hasSum_nat_add_iff' (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) 1).mpr hasSum_zeta_two
    simpa using this
  unfold zetaR
  have hle : ∀ n : ℕ, (1 : ℝ) / ((n : ℝ) + 1) ^ M ≤ 1 / ((n : ℝ) + 1) ^ 2 := fun n => by
    have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ h1 hM)
  have hsumM : Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1) ^ M) :=
    Summable.of_nonneg_of_le (fun n => by positivity) hle hs2.summable
  calc ∑' n : ℕ, (1 : ℝ) / ((n : ℝ) + 1) ^ M ≤ ∑' n : ℕ, (1 : ℝ) / ((n : ℝ) + 1) ^ 2 :=
        hsumM.tsum_le_tsum hle hs2.summable
    _ = Real.pi ^ 2 / 6 := hs2.tsum_eq
    _ ≤ 2 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
end Formalism.LogVandermondeBounds.StandardLattice
