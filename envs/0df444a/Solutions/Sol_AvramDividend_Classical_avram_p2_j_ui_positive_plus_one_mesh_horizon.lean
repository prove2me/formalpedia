-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_j_ui_positive_plus_one_mesh_horizon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T18:57:29.662052+00:00
-- url     : https://prove2.me/submissions/6b5456a8-6073-450e-83f6-00f755913e35

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.NhdsWithin
import Mathlib.Tactic.Positivity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Set Topology
open scoped BigOperators

/-! A positive uniform n+1-interval horizon mesh tends to zero through positive widths. -/
theorem solution
    (T : ℝ) (hT : 0 < T) :
    Tendsto (fun n : ℕ => T / ((n : ℝ) + 1)) atTop
      (nhdsWithin (0 : ℝ) (Ioi 0)) ∧
    (∀ n : ℕ, (((n + 1 : ℕ) : ℝ) *
      (T / ((n : ℝ) + 1))) = T) := by
  have hbase : Tendsto (fun n : ℕ =>
      (1 : ℝ) / ((n : ℝ) + 1)) atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hzero : Tendsto (fun n : ℕ =>
      T / ((n : ℝ) + 1)) atTop (nhds 0) := by
    have hmul : Tendsto (fun n : ℕ =>
        T * ((1 : ℝ) / ((n : ℝ) + 1))) atTop (nhds (T * 0)) :=
      tendsto_const_nhds.mul hbase
    simpa [div_eq_mul_inv] using hmul
  constructor
  · refine tendsto_nhdsWithin_iff.mpr ⟨hzero, Eventually.of_forall ?_⟩
    intro n
    change 0 < T / ((n : ℝ) + 1)
    exact div_pos hT (by positivity)
  · intro n
    have hden : (n : ℝ) + 1 ≠ 0 := by positivity
    norm_cast
    field_simp [hden]
