-- Prove2me | solution 1 for FD1D.V5.LocalBellman.Normalized.uniform_hMinus
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:26:43.008121+00:00
-- url     : https://prove2.me/submissions/f7e1dcb0-a57a-4232-b9f1-066d4b5e0014

import Definitions.Def_FD1D_V5_LocalInvariants
import Definitions.Def_FD1D_V5_LocalBellman

set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.LocalBellman
noncomputable section
open LocalPolicy
open FD1D.V5.LocalBellman.Normalized
namespace FD1D.V5.LocalBellman.Normalized
theorem _root_.solution {s ρ : ℝ}
    (hs : 0 < s) (hρ1 : ρ ≠ 1) :
    hMinus s ρ (uniform s ρ) = 1 := by
  unfold hMinus uniform
  have hsub : 1 - ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm hρ1)
  field_simp [hs.ne', hsub]
end FD1D.V5.LocalBellman.Normalized
