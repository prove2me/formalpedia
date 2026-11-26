-- Prove2me | solution 1 for FD1D.V5.LocalBellman.Normalized.lambda_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:26:33.013288+00:00
-- url     : https://prove2.me/submissions/1b6abac6-5298-466e-bd7f-642cfa7cc76a

import Definitions.Def_FD1D_V5_LocalInvariants
import Definitions.Def_FD1D_V5_LocalBellman

set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.LocalBellman
noncomputable section
open LocalPolicy
open FD1D.V5.LocalBellman.Normalized
namespace FD1D.V5.LocalBellman.Normalized
theorem _root_.solution (ρ : ℝ) :
    0 ≤ lambda ρ := by
  exact sq_nonneg ρ
end FD1D.V5.LocalBellman.Normalized
