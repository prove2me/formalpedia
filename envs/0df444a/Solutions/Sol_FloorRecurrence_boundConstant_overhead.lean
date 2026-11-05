-- Prove2me | solution 1 for FloorRecurrence.boundConstant_overhead
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.154279+00:00
-- url     : https://prove2.me/submissions/70c4e6e1-7827-4e8a-8f58-3ef191db2983

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
    C ≤ boundConstant m f C γ * (1 - γ) := by
  have hgap : 0 < 1 - γ := by linarith
  have hsum : 0 ≤ ∑ e ∈ Finset.range m, |f e| :=
    Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hle : |C| / (1 - γ) ≤ boundConstant m f C γ := by unfold boundConstant; linarith
  have h := mul_le_mul_of_nonneg_right hle hgap.le
  rw [div_mul_cancel₀ _ hgap.ne'] at h
  exact (le_abs_self C).trans h
end FloorRecurrence
