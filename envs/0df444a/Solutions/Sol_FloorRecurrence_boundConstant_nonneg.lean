-- Prove2me | solution 1 for FloorRecurrence.boundConstant_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.154279+00:00
-- url     : https://prove2.me/submissions/f7843ec1-5538-4724-be93-6e6a7710c3b8

import Definitions.Def_FloorDepth
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_FloorRecurrence

set_option autoImplicit true
open FloorRecurrence
open scoped BigOperators
namespace FloorRecurrence
theorem _root_.solution (m : ℕ) (f : ℕ → ℝ) (C γ : ℝ) (hγ : γ < 1) :
    0 ≤ boundConstant m f C γ := by
  unfold boundConstant
  exact add_nonneg (Finset.sum_nonneg (fun _ _ => abs_nonneg _))
    (div_nonneg (abs_nonneg _) (by linarith))
end FloorRecurrence
