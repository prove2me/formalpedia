-- Prove2me | solution 1 for FD1D.depthTarget_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:13:19.887015+00:00
-- url     : https://prove2.me/submissions/f1a80b7b-751a-4a98-b6d1-d0a7fb6ff065

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Parameters
import Theorems.Thm_FD1D_depthTarget_pos

set_option autoImplicit true
open FD1D
noncomputable section
open Filter Asymptotics
namespace FD1D
theorem _root_.solution (m : ℕ) :
    depthTarget m ≠ 0 :=
  (depthTarget_pos m).ne'
end FD1D
