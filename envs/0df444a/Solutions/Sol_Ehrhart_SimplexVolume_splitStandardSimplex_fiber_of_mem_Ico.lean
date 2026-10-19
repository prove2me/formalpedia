-- Prove2me | solution 1 for Ehrhart.SimplexVolume.splitStandardSimplex_fiber_of_mem_Ico
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:11.14329+00:00
-- url     : https://prove2.me/submissions/5911d214-6683-4f30-b293-ee65a8db1dab

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.SimplexVolume
open Set MeasureTheory
open scoped BigOperators ENNReal Pointwise
namespace Ehrhart.SimplexVolume
theorem _root_.solution (n : ℕ) {t : ℝ}
    (ht : t ∈ Set.Ico (0 : ℝ) 1) :
    Prod.mk t ⁻¹' splitStandardSimplex n =
      (1 - t) • standardSimplex n := by
  have hscale : 0 < 1 - t := sub_pos.mpr ht.2
  ext x
  change
    (0 ≤ t ∧ (∀ i, 0 ≤ x i) ∧ t + (∑ i, x i) ≤ 1) ↔
      x ∈ (1 - t) • standardSimplex n
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hscale.ne']
  change
    (0 ≤ t ∧ (∀ i, 0 ≤ x i) ∧ t + (∑ i, x i) ≤ 1) ↔
      (∀ i, 0 ≤ (1 - t)⁻¹ * x i) ∧
        (∑ i, (1 - t)⁻¹ * x i) ≤ 1
  constructor
  · rintro ⟨_, hx, hsum⟩
    refine ⟨fun i => mul_nonneg (inv_nonneg.mpr hscale.le) (hx i), ?_⟩
    rw [← Finset.mul_sum, inv_mul_le_one₀ hscale]
    linarith
  · rintro ⟨hx, hsum⟩
    refine ⟨ht.1, fun i =>
      (mul_nonneg_iff_of_pos_left (inv_pos.mpr hscale)).mp (hx i), ?_⟩
    rw [← Finset.mul_sum, inv_mul_le_one₀ hscale] at hsum
    linarith
end Ehrhart.SimplexVolume
