-- Prove2me | solution 1 for FD1D.V5.LocalBellman.Normalized.lambda_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:26:54.181796+00:00
-- url     : https://prove2.me/submissions/1a1f3910-49c7-41c6-92b8-41cdadbc1a56

import Definitions.Def_FD1D_V5_LocalInvariants
import Definitions.Def_FD1D_V5_LocalBellman

set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.LocalBellman
noncomputable section
open LocalPolicy
open FD1D.V5.LocalBellman.Normalized
namespace FD1D.V5.LocalBellman.Normalized
theorem _root_.solution {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    lambda ρ < 1 := by
  unfold lambda
  nlinarith [sq_nonneg ρ]
end FD1D.V5.LocalBellman.Normalized
