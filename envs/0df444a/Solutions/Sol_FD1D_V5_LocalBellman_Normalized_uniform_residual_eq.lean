-- Prove2me | solution 1 for FD1D.V5.LocalBellman.Normalized.uniform_residual_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:49:26.226025+00:00
-- url     : https://prove2.me/submissions/2add6006-9f47-4318-90e9-812b4b92769a

import Definitions.Def_FD1D_V5_LocalInvariants
import Definitions.Def_FD1D_V5_LocalBellman
import Theorems.Thm_FD1D_V5_LocalBellman_Normalized_lambda_lt_one
import Theorems.Thm_FD1D_V5_LocalBellman_Normalized_d_pos
import Theorems.Thm_FD1D_V5_LocalBellman_Normalized_uniform_hPlus
import Theorems.Thm_FD1D_V5_LocalBellman_Normalized_uniform_hMinus

set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.LocalBellman
noncomputable section
open LocalPolicy
open FD1D.V5.LocalBellman.Normalized
namespace FD1D.V5.LocalBellman.Normalized
theorem _root_.solution
    {s r ρ : ℝ}
    (hs : 0 < s) (hr0 : -s < r) (hr1 : r ≤ 1 / 2)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    residual s r ρ (uniform s ρ) =
      r ^ 2 / 8 - (uniform s ρ) ^ 2 / 24 +
        g s r ^ 2 * (uniform s ρ) ^ 2 /
          (d s ρ * (s + 1 / 2)) +
        g s r * (1 / 2 - r) * (s + 1) /
          (2 * d s ρ * (s + 1 / 2)) := by
  have hs0 : s ≠ 0 := hs.ne'
  have hsHalf : s + 1 / 2 ≠ 0 := by linarith
  have hp : s * (1 + ρ) + 1 ≠ 0 := by
    have : 0 < s * (1 + ρ) + 1 := by positivity
    exact this.ne'
  have hm : s * (1 - ρ) + 1 ≠ 0 := by
    have : 0 < s * (1 - ρ) + 1 := by
      have := lambda_lt_one hρ0 hρ1
      nlinarith [sq_nonneg ρ]
    exact this.ne'
  have hd : d s ρ ≠ 0 := (d_pos hs hρ0 hρ1).ne'
  unfold residual tPlus tMinus ZPlus ZMinus ZParent
  rw [uniform_hPlus hs (by linarith), uniform_hMinus hs (by linarith)]
  unfold bellman uniform g
  field_simp [hs0, hsHalf, hp, hm, hd]
  unfold d A lambda
  ring
end FD1D.V5.LocalBellman.Normalized
