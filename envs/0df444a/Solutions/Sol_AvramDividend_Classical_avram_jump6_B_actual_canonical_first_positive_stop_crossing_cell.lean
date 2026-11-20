-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_actual_canonical_first_positive_stop_crossing_cell
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T19:57:13.077598+00:00
-- url     : https://prove2.me/submissions/940bd271-8995-4c1f-8f91-633cef99e179

import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Order.Filter.Defs
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_actual_canonical_grid_monotone_zero_and_reaches_stop_v2
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal
noncomputable section
set_option autoImplicit false

theorem solution
    (n j : ℕ) (ρ : ℝ≥0)
    (hρ : 0 < ρ) (hρn : ρ ≤ (n : ℝ≥0)) :
    ∃ i : ℕ, i < (n + 1) * (j + 1) ∧
      min ((i : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) ρ < ρ ∧
      min (((i + 1 : ℕ) : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) ρ = ρ := by
  let v : ℕ → ℝ≥0 := fun i =>
    min ((i : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) ρ
  let m : ℕ := (n + 1) * (j + 1)
  obtain ⟨hvmono, hv0, hvm⟩ :=
    avram_jump6_B_actual_canonical_grid_monotone_zero_and_reaches_stop_v2
      n j ρ hρn
  have hex : ∃ k : ℕ, v k = ρ := ⟨m, hvm⟩
  let k := Nat.find hex
  have hk : v k = ρ := Nat.find_spec hex
  have hkpos : 0 < k := by
    by_contra h
    have hzero : k = 0 := Nat.eq_zero_of_not_pos h
    have hv : v 0 = 0 := hv0
    rw [hzero, hv] at hk
    exact (ne_of_gt hρ) hk.symm
  have hkm : k ≤ m := Nat.find_min' hex hvm
  let i := k - 1
  have hiadd : i + 1 = k := Nat.sub_add_cancel hkpos
  have him : i < m := by omega
  have hile : v i ≤ ρ := by
    calc
      v i ≤ v k := hvmono (by omega)
      _ = ρ := hk
  have hine : v i ≠ ρ := by
    intro heq
    have hminimal : k ≤ i := Nat.find_min' hex heq
    omega
  have hilt : v i < ρ := lt_of_le_of_ne hile hine
  refine ⟨i, him, hilt, ?_⟩
  change v (i + 1) = ρ
  rw [hiadd]
  exact hk
