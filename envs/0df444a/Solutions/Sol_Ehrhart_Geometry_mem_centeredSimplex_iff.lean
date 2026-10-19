-- Prove2me | solution 1 for Ehrhart.Geometry.mem_centeredSimplex_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:10.440282+00:00
-- url     : https://prove2.me/submissions/a5d64049-3345-4bfb-88ad-0492d800a225

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.Geometry
open Set MeasureTheory
open scoped BigOperators
namespace Ehrhart.Geometry
theorem _root_.solution {n : ℕ} {y : Space n} :
    y ∈ centeredSimplex n ↔
      (∀ i, -(1 : ℝ) ≤ y i) ∧ (∑ i, y i) ≤ 1 := by
  classical
  have hc : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  constructor
  · rintro ⟨x, hx, rfl⟩
    change (∀ i, -(1 : ℝ) ≤ ((n : ℝ) + 1) * x i - 1) ∧
      (∑ i, (((n : ℝ) + 1) * x i - 1)) ≤ 1
    constructor
    · intro i
      have hp := mul_nonneg hc.le (hx.1 i)
      linarith
    · have hsum : ((n : ℝ) + 1) * (∑ i, x i) ≤ (n : ℝ) + 1 :=
        (mul_le_mul_of_nonneg_left hx.2 hc.le).trans_eq (mul_one _)
      simpa [Finset.sum_sub_distrib, ← Finset.mul_sum] using
        (show ((n : ℝ) + 1) * (∑ i, x i) - (n : ℝ) ≤ 1 by linarith)
  · rintro ⟨hy, hsum⟩
    let x : Space n := fun i => (y i + 1) / ((n : ℝ) + 1)
    refine ⟨x, ⟨?_, ?_⟩, ?_⟩
    · intro i
      exact div_nonneg (by linarith [hy i]) hc.le
    · change (∑ i, (y i + 1) / ((n : ℝ) + 1)) ≤ 1
      rw [← Finset.sum_div, div_le_iff₀ hc]
      simpa [Finset.sum_add_distrib] using
        (show (∑ i, y i) + (n : ℝ) ≤ (n : ℝ) + 1 by linarith)
    · funext i
      change ((n : ℝ) + 1) * ((y i + 1) / ((n : ℝ) + 1)) - 1 = y i
      field_simp
      ring
end Ehrhart.Geometry
