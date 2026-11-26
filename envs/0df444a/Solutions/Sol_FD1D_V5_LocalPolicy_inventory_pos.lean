-- Prove2me | solution 1 for FD1D.V5.LocalPolicy.inventory_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:19:45.386087+00:00
-- url     : https://prove2.me/submissions/0f71c314-0a12-4ad7-a6dd-8175a7b48cfe

import Definitions.Def_FD1D_V5_Parameters
import Definitions.Def_FD1D_V5_LocalPolicy

set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.LocalPolicy
noncomputable section
namespace FD1D.V5.LocalPolicy
theorem _root_.solution {x y : ℕ} (hne : x + y ≠ 0) :
    0 < inventory x y := by
  unfold inventory
  exact_mod_cast Nat.pos_of_ne_zero hne
end FD1D.V5.LocalPolicy
