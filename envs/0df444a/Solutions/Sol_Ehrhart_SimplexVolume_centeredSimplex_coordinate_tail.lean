-- Prove2me | solution 1 for Ehrhart.SimplexVolume.centeredSimplex_coordinate_tail
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:11.14329+00:00
-- url     : https://prove2.me/submissions/3c8a9dc0-11b7-4ea9-8a05-51f501847e84

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
theorem _root_.solution {n : ℕ}
    (T : Set (Space n))
    (hT : ∀ y, y ∈ T ↔
      (∀ j, -(1 : ℝ) ≤ y j) ∧ (∑ j, y j) ≤ 1)
    (i : Fin n) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < (n : ℝ) + 1) :
    {y : Space n | y ∈ T ∧ t ≤ y i + 1} =
      (fun x : Space n => x + (Pi.single i t - 1)) ''
        (((n : ℝ) + 1 - t) • standardSimplex n) := by
  classical
  let v : Space n := Pi.single i t
  let b : Space n := v - 1
  have hvsum : (∑ j, v j) = t := by simp [v, Pi.single_apply]
  have hbsum : (∑ j, b j) = t - n := by
    simp [b, Finset.sum_sub_distrib, hvsum]
  have hvnonneg (j : Fin n) : 0 ≤ v j := by
    by_cases hji : j = i
    · subst j
      simpa [v] using ht0
    · simp [v, hji]
  have hp : 0 < (n : ℝ) + 1 - t := sub_pos.mpr ht1
  ext y
  change (y ∈ T ∧ t ≤ y i + 1) ↔
    y ∈ (fun x : Space n => x + b) ''
      (((n : ℝ) + 1 - t) • standardSimplex n)
  constructor
  · rintro ⟨hy, hyt⟩
    have hy' := (hT y).mp hy
    refine ⟨y - b, ?_, by ext j; simp⟩
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ hp.ne']
    change (∀ j, 0 ≤ ((n : ℝ) + 1 - t)⁻¹ * (y j - b j)) ∧
      (∑ j, ((n : ℝ) + 1 - t)⁻¹ * (y j - b j)) ≤ 1
    constructor
    · intro j
      refine mul_nonneg (inv_nonneg.mpr hp.le) ?_
      by_cases hji : j = i
      · subst j
        simp only [b, Pi.sub_apply, v, Pi.single_eq_same, Pi.one_apply]
        linarith
      · simp only [b, Pi.sub_apply, v, Pi.single_apply, if_neg hji,
          Pi.one_apply]
        linarith [hy'.1 j]
    · rw [← Finset.mul_sum, Finset.sum_sub_distrib, hbsum,
        inv_mul_le_one₀ hp]
      linarith [hy'.2]
  · rintro ⟨x, hx, rfl⟩
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ hp.ne'] at hx
    change (∀ j, 0 ≤ ((n : ℝ) + 1 - t)⁻¹ * x j) ∧
      (∑ j, ((n : ℝ) + 1 - t)⁻¹ * x j) ≤ 1 at hx
    have hx0 (j : Fin n) : 0 ≤ x j :=
      (mul_nonneg_iff_of_pos_left (inv_pos.mpr hp)).mp (hx.1 j)
    have hxsum : (∑ j, x j) ≤ (n : ℝ) + 1 - t := by
      rw [← Finset.mul_sum, inv_mul_le_one₀ hp] at hx
      exact hx.2
    refine ⟨(hT (x + b)).mpr ⟨?_, ?_⟩, ?_⟩
    · intro j
      change -(1 : ℝ) ≤ x j + (v j - 1)
      linarith [hx0 j, hvnonneg j]
    · simp only [Pi.add_apply, Finset.sum_add_distrib, hbsum]
      linarith
    · change t ≤ (x + b) i + 1
      simp only [Pi.add_apply, b, Pi.sub_apply, v, Pi.single_eq_same,
        Pi.one_apply]
      linarith [hx0 i]
end Ehrhart.SimplexVolume
