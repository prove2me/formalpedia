-- Prove2me | solution 1 for FloorRecurrence.boundConstant_base
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.154279+00:00
-- url     : https://prove2.me/submissions/3c2b53b4-d787-496d-9ecd-421e589c47fe

import Definitions.Def_FloorDepth
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_FloorRecurrence
import Theorems.Thm_FloorRecurrence_one_le_width_power
import Theorems.Thm_FloorRecurrence_boundConstant_nonneg

set_option autoImplicit true
open FloorRecurrence
open scoped BigOperators
namespace FloorRecurrence
theorem _root_.solution (m : ℕ) (f : ℕ → ℝ) (C γ p : ℝ)
    (hγ : γ < 1) (hp : 0 ≤ p) (e : ℕ) (he : 0 < e) (hem : e < m) :
    f e ≤ boundConstant m f C γ * (e : ℝ) ^ p := by
  have hsum : |f e| ≤ ∑ k ∈ Finset.range m, |f k| :=
    Finset.single_le_sum (fun k (_ : k ∈ Finset.range m) => abs_nonneg (f k))
      (Finset.mem_range.mpr hem)
  have hquot : 0 ≤ |C| / (1 - γ) := div_nonneg (abs_nonneg _) (by linarith)
  have hbase : f e ≤ boundConstant m f C γ := by
    unfold boundConstant
    linarith [le_abs_self (f e)]
  exact hbase.trans (by
    simpa using mul_le_mul_of_nonneg_left
      (one_le_width_power e p he hp) (boundConstant_nonneg m f C γ hγ))
end FloorRecurrence
