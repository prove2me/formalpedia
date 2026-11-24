-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.A5.sum_dif_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:42:27.747889+00:00
-- url     : https://prove2.me/submissions/b501bd34-3c86-4add-845c-b2149b7dfb3d

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SummableSqGeom
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_A5_summable_sq_geom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Finset
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.A5
variable {ι : Type*}
variable {q : ι → ℝ}
namespace Formalism.HermitianLattices.Ext.L3.A5
theorem _root_.solution (hq : ∀ i, 2 ≤ q i) {R : ι → ℕ → ℝ}
    (hRb : ∀ i j, |R i (j + 1) - R i j| ≤ 8 * ((j : ℝ) + 2) ^ 2 / q i) (i : ι) (J : ℕ) :
    ∑ j ∈ range (J + 1), |dif R i j| / q i ^ j ≤ 1 + cGeom * (q i ^ 2)⁻¹ := by
  have hq0 : 0 < q i := by linarith [hq i]
  rw [Finset.sum_range_succ']
  simp only [dif, pow_zero, div_one, abs_one]
  rw [add_comm]
  refine add_le_add le_rfl ?_
  have hterm : ∀ j ∈ range J, |R i (j + 1) - R i j| / q i ^ (j + 1) ≤
      (q i ^ 2)⁻¹ * (8 * ((j : ℝ) + 2) ^ 2 * (1 / 2 : ℝ) ^ j) := by
    intro j _
    have hqj : 0 < q i ^ (j + 1) := pow_pos hq0 _
    have hqne : q i ≠ 0 := hq0.ne'
    rw [div_le_iff₀ hqj]
    have hx : 1 ≤ (q i / 2) ^ j := one_le_pow₀ (by linarith [hq i])
    have hc : 0 ≤ 8 * ((j : ℝ) + 2) ^ 2 := by positivity
    have e : (q i ^ 2)⁻¹ * (8 * ((j : ℝ) + 2) ^ 2 * (1 / 2 : ℝ) ^ j) * q i ^ (j + 1) =
        8 * ((j : ℝ) + 2) ^ 2 * (q i / 2) ^ j / q i := by
      have h2 : (q i ^ 2)⁻¹ * q i ^ (j + 1) = q i ^ j / q i := by
        rw [pow_succ (q i) j, sq]
        first
          | (field_simp; ring)
          | field_simp
      calc (q i ^ 2)⁻¹ * (8 * ((j : ℝ) + 2) ^ 2 * (1 / 2 : ℝ) ^ j) * q i ^ (j + 1)
          = 8 * ((j : ℝ) + 2) ^ 2 * (1 / 2 : ℝ) ^ j * ((q i ^ 2)⁻¹ * q i ^ (j + 1)) := by ring
        _ = 8 * ((j : ℝ) + 2) ^ 2 * ((1 / 2 : ℝ) ^ j * q i ^ j) / q i := by rw [h2]; ring
        _ = 8 * ((j : ℝ) + 2) ^ 2 * (q i / 2) ^ j / q i := by rw [← mul_pow]; ring_nf
    rw [e]
    calc |R i (j + 1) - R i j| ≤ 8 * ((j : ℝ) + 2) ^ 2 / q i := hRb i j
      _ ≤ 8 * ((j : ℝ) + 2) ^ 2 * (q i / 2) ^ j / q i := by
        first
          | exact div_le_div_of_nonneg_right (le_mul_of_one_le_right hc hx) hq0.le
          | exact (div_le_div_iff_of_pos_right hq0).mpr (le_mul_of_one_le_right hc hx)
          | exact (div_le_div_right hq0).mpr (le_mul_of_one_le_right hc hx)
  calc ∑ j ∈ range J, |R i (j + 1) - R i j| / q i ^ (j + 1)
      ≤ ∑ j ∈ range J, (q i ^ 2)⁻¹ * (8 * ((j : ℝ) + 2) ^ 2 * (1 / 2 : ℝ) ^ j) :=
        Finset.sum_le_sum hterm
    _ = (q i ^ 2)⁻¹ * ∑ j ∈ range J, 8 * ((j : ℝ) + 2) ^ 2 * (1 / 2 : ℝ) ^ j := by
        rw [Finset.mul_sum]
    _ ≤ (q i ^ 2)⁻¹ * cGeom := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact summable_sq_geom.sum_le_tsum _ (fun j _ => by positivity)
    _ = cGeom * (q i ^ 2)⁻¹ := mul_comm _ _
end Formalism.HermitianLattices.Ext.L3.A5
