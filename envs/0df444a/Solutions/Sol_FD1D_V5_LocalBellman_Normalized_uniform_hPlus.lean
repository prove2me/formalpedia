-- Prove2me | solution 1 for FD1D.V5.LocalBellman.Normalized.uniform_hPlus
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:26:37.967798+00:00
-- url     : https://prove2.me/submissions/df5b9417-9bdd-4952-935d-1491e520d8bb

import Definitions.Def_FD1D_V5_LocalInvariants
import Definitions.Def_FD1D_V5_LocalBellman

set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.LocalBellman
noncomputable section
open LocalPolicy
open FD1D.V5.LocalBellman.Normalized
namespace FD1D.V5.LocalBellman.Normalized
theorem _root_.solution {s ρ : ℝ}
    (hs : 0 < s) (hρ1 : ρ ≠ -1) :
    hPlus s ρ (uniform s ρ) = 1 := by
  unfold hPlus uniform
  have hsum : 1 + ρ ≠ 0 := by
    intro h
    exact hρ1 (by linarith)
  field_simp [hs.ne', hsum]
end FD1D.V5.LocalBellman.Normalized
