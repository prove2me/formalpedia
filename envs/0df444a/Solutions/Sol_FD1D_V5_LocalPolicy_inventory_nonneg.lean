-- Prove2me | solution 1 for FD1D.V5.LocalPolicy.inventory_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:19:10.15368+00:00
-- url     : https://prove2.me/submissions/46aa51ce-fa28-4e9f-842b-53d3beaea943

import Definitions.Def_FD1D_V5_Parameters
import Definitions.Def_FD1D_V5_LocalPolicy

set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.LocalPolicy
noncomputable section
namespace FD1D.V5.LocalPolicy
theorem _root_.solution (x y : ℕ) :
    0 ≤ inventory x y := by
  unfold inventory
  positivity
end FD1D.V5.LocalPolicy
