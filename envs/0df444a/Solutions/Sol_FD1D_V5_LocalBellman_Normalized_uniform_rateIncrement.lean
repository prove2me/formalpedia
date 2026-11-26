-- Prove2me | solution 1 for FD1D.V5.LocalBellman.Normalized.uniform_rateIncrement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:49:19.31209+00:00
-- url     : https://prove2.me/submissions/60126982-f0c0-46c9-9551-22f04b53bb29

import Definitions.Def_FD1D_V5_LocalInvariants
import Definitions.Def_FD1D_V5_LocalBellman
import Theorems.Thm_FD1D_V5_LocalBellman_Normalized_uniform_hPlus
import Theorems.Thm_FD1D_V5_LocalBellman_Normalized_uniform_hMinus

set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.LocalBellman
noncomputable section
open LocalPolicy
open FD1D.V5.LocalBellman.Normalized
namespace FD1D.V5.LocalBellman.Normalized
theorem _root_.solution {s ρ : ℝ}
    (hs : 0 < s) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    rateIncrement s ρ (uniform s ρ) = 0 := by
  rw [rateIncrement, uniform_hPlus hs (by linarith),
    uniform_hMinus hs (by linarith)]
  norm_num
end FD1D.V5.LocalBellman.Normalized
