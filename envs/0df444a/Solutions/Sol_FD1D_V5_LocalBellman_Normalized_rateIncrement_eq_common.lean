-- Prove2me | solution 1 for FD1D.V5.LocalBellman.Normalized.rateIncrement_eq_common
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:49:17.252323+00:00
-- url     : https://prove2.me/submissions/b1ff2111-2919-449f-9f58-9ccc0b766273

import Definitions.Def_FD1D_V5_LocalInvariants
import Definitions.Def_FD1D_V5_LocalBellman
import Theorems.Thm_FD1D_V5_LocalBellman_Normalized_lambda_lt_one
import Theorems.Thm_FD1D_V5_LocalBellman_Normalized_A_pos

set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.LocalBellman
noncomputable section
open LocalPolicy
open FD1D.V5.LocalBellman.Normalized
namespace FD1D.V5.LocalBellman.Normalized
theorem _root_.solution
    {s ρ k : ℝ}
    (hs : 0 < s) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    rateIncrement s ρ (ρ * k) =
      2 * lambda ρ * J s ρ k +
        (1 + lambda ρ) * lambda ρ * J s ρ k ^ 2 := by
  have hs0 : s ≠ 0 := hs.ne'
  have hA : A s ρ ≠ 0 := (A_pos hs hρ0 hρ1).ne'
  have hρp : 1 + ρ ≠ 0 := by
    have := lambda_lt_one hρ0 hρ1
    nlinarith [sq_nonneg ρ]
  have hρm : 1 - ρ ≠ 0 := by linarith
  unfold rateIncrement hPlus hMinus J
  field_simp [hs0, hA, hρp, hρm]
  unfold A lambda
  ring
end FD1D.V5.LocalBellman.Normalized
