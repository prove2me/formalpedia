-- Prove2me | solution 1 for FD1D.V5.LocalBellman.Normalized.d_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:29:48.928425+00:00
-- url     : https://prove2.me/submissions/00b04d36-dd1e-4e7f-b943-e406689f9f26

import Definitions.Def_FD1D_V5_LocalInvariants
import Definitions.Def_FD1D_V5_LocalBellman
import Theorems.Thm_FD1D_V5_LocalBellman_Normalized_A_pos

set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.LocalBellman
noncomputable section
open LocalPolicy
open FD1D.V5.LocalBellman.Normalized
namespace FD1D.V5.LocalBellman.Normalized
theorem _root_.solution {s ρ : ℝ} (hs : 0 < s) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    0 < d s ρ := by
  have hA := (A_pos hs hρ0 hρ1).le
  unfold d
  positivity
end FD1D.V5.LocalBellman.Normalized
