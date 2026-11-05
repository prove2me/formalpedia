-- Prove2me | solution 1 for FloorRecurrence.all_width_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.154279+00:00
-- url     : https://prove2.me/submissions/4d84194d-ec34-4aa6-9aa0-97b48284c8b0

import Definitions.Def_FloorDepth
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_FloorRecurrence
import Theorems.Thm_FloorRecurrence_floor_child_power
import Theorems.Thm_FloorRecurrence_one_le_width_power
import Theorems.Thm_FloorDepth_child_pos


set_option autoImplicit true
open FloorRecurrence
open scoped BigOperators
namespace FloorRecurrence
theorem _root_.solution {ι : Type} (rows : List ι) (c : ι → ℝ) (t : ι → ℕ)
    (m : ℕ) (f : ℕ → ℝ) (p A C γ : ℝ)
    (hm : 0 < m) (hp : 0 ≤ p) (hA : 0 ≤ A)
    (hc : ∀ i ∈ rows, 0 ≤ c i) (ht : ∀ i ∈ rows, 0 < t i)
    (htm : ∀ i ∈ rows, t i < m)
    (hγ : γ = (rows.map (fun i => c i * ((t i : ℝ) / m) ^ p)).sum)
    (hγ1 : γ < 1) (overhead : C ≤ A * (1 - γ))
    (base : ∀ e, 0 < e → e < m → f e ≤ A * (e : ℝ) ^ p)
    (physical_recurrence : ∀ e, m ≤ e →
      f e ≤ C + (rows.map (fun i => c i * f (t i * (e / m)))).sum) :
    ∀ e, 0 < e → f e ≤ A * (e : ℝ) ^ p := by
  intro e
  induction e using Nat.strong_induction_on with
  | h e ih =>
    intro he
    by_cases hbase : e < m
    · exact base e he hbase
    · have hem : m ≤ e := Nat.le_of_not_gt hbase
      have hrow : ∀ i ∈ rows, c i * f (t i * (e / m)) ≤
          c i * (A * (((t i : ℝ) / m) ^ p * (e : ℝ) ^ p)) := by
        intro i hi
        have hchild := ih (FloorDepth.child m (t i) e)
          (FloorDepth.child_lt m (t i) e (htm i hi) hem)
          (FloorDepth.child_pos m (t i) e hm (ht i hi) hem)
        exact mul_le_mul_of_nonneg_left
          (hchild.trans (mul_le_mul_of_nonneg_left (floor_child_power m (t i) e p hm hp) hA))
          (hc i hi)
      have hsum : (rows.map (fun i => c i * (A * (((t i : ℝ) / m) ^ p * (e : ℝ) ^ p)))).sum =
          A * γ * (e : ℝ) ^ p := by
        calc
          _ = (rows.map (fun i => (c i * ((t i : ℝ) / m) ^ p) * (A * (e : ℝ) ^ p))).sum := by
            congr 1
            apply List.map_congr_left
            intro i hi
            ring
          _ = γ * (A * (e : ℝ) ^ p) := by rw [List.sum_map_mul_right, ← hγ]
          _ = _ := by ring
      have hgap : 0 ≤ A * (1 - γ) := mul_nonneg hA (by linarith)
      have hpaid : C ≤ A * (1 - γ) * (e : ℝ) ^ p :=
        overhead.trans (by simpa using mul_le_mul_of_nonneg_left (one_le_width_power e p he hp) hgap)
      calc
        f e ≤ C + (rows.map (fun i => c i * f (t i * (e / m)))).sum := physical_recurrence e hem
        _ ≤ C + (rows.map (fun i => c i * (A * (((t i : ℝ) / m) ^ p * (e : ℝ) ^ p)))).sum :=
          add_le_add (le_refl C) (List.sum_le_sum hrow)
        _ = C + A * γ * (e : ℝ) ^ p := by rw [hsum]
        _ ≤ A * (e : ℝ) ^ p := by nlinarith [hpaid]
end FloorRecurrence
