-- Prove2me | solution 1 for FD1D.V5.LocalBellman.Normalized.residual_eq_common
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:31:31.38043+00:00
-- url     : https://prove2.me/submissions/b3273844-7e84-4a9b-a571-6529d4f22e1b

import Definitions.Def_FD1D_V5_LocalInvariants
import Definitions.Def_FD1D_V5_LocalBellman
import Theorems.Thm_FD1D_V5_LocalBellman_Normalized_lambda_lt_one
import Theorems.Thm_FD1D_V5_LocalBellman_Normalized_A_pos
import Theorems.Thm_FD1D_V5_LocalBellman_Normalized_d_pos

set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.LocalBellman
noncomputable section
open LocalPolicy
open FD1D.V5.LocalBellman.Normalized
namespace FD1D.V5.LocalBellman.Normalized
theorem _root_.solution
    {s r ρ k : ℝ}
    (hs : 0 < s) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    residual s r ρ (ρ * k) =
      r ^ 2 / 8 - lambda ρ * k ^ 2 / 24 +
        g s r * (1 / 2 - r) * (s + 1) /
          (2 * d s ρ * (s + 1 / 2)) +
        lambda ρ * g s r / d s ρ * bracket s r ρ k := by
  have hs0 : s ≠ 0 := hs.ne'
  have hA : A s ρ ≠ 0 := (A_pos hs hρ0 hρ1).ne'
  have hd : d s ρ ≠ 0 := (d_pos hs hρ0 hρ1).ne'
  have hsHalf : s + 1 / 2 ≠ 0 := by linarith
  have hρp : 1 + ρ ≠ 0 := by
    have := lambda_lt_one hρ0 hρ1
    nlinarith [sq_nonneg ρ]
  have hρm : 1 - ρ ≠ 0 := by linarith
  have hp : s * (1 + ρ) + 1 ≠ 0 := by
    have : 0 < s * (1 + ρ) + 1 := by positivity
    exact this.ne'
  have hm : s * (1 - ρ) + 1 ≠ 0 := by
    have : 0 < s * (1 - ρ) + 1 := by positivity
    exact this.ne'
  unfold residual tPlus tMinus hPlus hMinus
    ZPlus ZMinus ZParent bellman bracket J
  field_simp [hs0, hA, hd, hsHalf, hρp, hρm, hp, hm]
  unfold d A lambda g
  ring
end FD1D.V5.LocalBellman.Normalized
