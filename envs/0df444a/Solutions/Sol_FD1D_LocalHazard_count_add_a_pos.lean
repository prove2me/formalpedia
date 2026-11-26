-- Prove2me | solution 1 for FD1D.LocalHazard.count_add_a_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:52:28.614796+00:00
-- url     : https://prove2.me/submissions/496f7f7f-4256-4fd0-826c-a620eabc11df

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Hazard

set_option autoImplicit true
open FD1D
noncomputable section
open FD1D.LocalHazard
namespace FD1D.LocalHazard
theorem _root_.solution {a : ℝ} (ha : 0 < a) (k : ℕ) : 0 < (k : ℝ) + a := by
  positivity
end FD1D.LocalHazard
