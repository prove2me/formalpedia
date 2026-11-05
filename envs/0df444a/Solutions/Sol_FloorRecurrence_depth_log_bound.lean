-- Prove2me | solution 1 for FloorRecurrence.depth_log_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.154279+00:00
-- url     : https://prove2.me/submissions/0ea0738b-4ed1-4dda-b315-f7d5868c30d2

import Definitions.Def_FloorDepth
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_FloorRecurrence
import Theorems.Thm_FloorRecurrence_floor_child_le_ratio
import Theorems.Thm_FloorDepth_child_pos
import Theorems.Thm_FloorDepth_depth_base
import Theorems.Thm_FloorDepth_depth_step


set_option autoImplicit true
open FloorRecurrence
open scoped BigOperators
namespace FloorRecurrence
theorem _root_.solution (m t : ℕ) (ht : t < m) (ht0 : 0 < t) :
    ∀ e, 0 < e → (FloorDepth.depth m t ht e : ℝ) ≤
      1 + Real.log (e : ℝ) / Real.log ((m : ℝ) / t) := by
  have hm : 0 < m := Nat.zero_lt_of_lt ht
  have htR : (0 : ℝ) < t := by exact_mod_cast ht0
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hratio : 1 < (m : ℝ) / t := (one_lt_div htR).mpr (by exact_mod_cast ht)
  have hlog : 0 < Real.log ((m : ℝ) / t) := Real.log_pos hratio
  intro e
  induction e using Nat.strong_induction_on with
  | h e ih =>
    intro he
    have heR : (0 : ℝ) < e := by exact_mod_cast he
    by_cases hb : e < m
    · rw [FloorDepth.depth_base m t ht e hb]
      have hlogE : 0 ≤ Real.log (e : ℝ) := Real.log_nonneg (by exact_mod_cast he)
      have hnonneg := div_nonneg hlogE hlog.le
      norm_num only [Nat.cast_zero]
      linarith
    · have hem : m ≤ e := Nat.le_of_not_gt hb
      have hc0 := FloorDepth.child_pos m t e hm ht0 hem
      have hcR : (0 : ℝ) < FloorDepth.child m t e := by exact_mod_cast hc0
      have ihc := ih (FloorDepth.child m t e) (FloorDepth.child_lt m t e ht hem) hc0
      have hl : Real.log (FloorDepth.child m t e : ℝ) ≤
          Real.log (e : ℝ) - Real.log ((m : ℝ) / t) := by
        have hmono := Real.log_le_log hcR (floor_child_le_ratio m t e hm)
        rw [Real.log_mul (div_pos htR hmR).ne' heR.ne',
          Real.log_div htR.ne' hmR.ne'] at hmono
        rw [Real.log_div hmR.ne' htR.ne']
        linarith
      have hd := (div_le_div_iff_of_pos_right hlog).mpr hl
      rw [sub_div, div_self hlog.ne'] at hd
      rw [FloorDepth.depth_step m t ht e hem, Nat.cast_add, Nat.cast_one]
      linarith
end FloorRecurrence
