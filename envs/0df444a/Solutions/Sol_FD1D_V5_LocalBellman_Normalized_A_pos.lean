-- Prove2me | solution 1 for FD1D.V5.LocalBellman.Normalized.A_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:28:37.401135+00:00
-- url     : https://prove2.me/submissions/65b65fdc-7aeb-4008-a1a9-e4fd102b1027

import Definitions.Def_FD1D_V5_LocalInvariants
import Definitions.Def_FD1D_V5_LocalBellman
import Theorems.Thm_FD1D_V5_LocalBellman_Normalized_lambda_lt_one

set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.LocalBellman
noncomputable section
open LocalPolicy
open FD1D.V5.LocalBellman.Normalized
namespace FD1D.V5.LocalBellman.Normalized
theorem _root_.solution {s ρ : ℝ} (hs : 0 < s) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    0 < A s ρ := by
  unfold A
  exact mul_pos hs (sub_pos.mpr (lambda_lt_one hρ0 hρ1))
end FD1D.V5.LocalBellman.Normalized
