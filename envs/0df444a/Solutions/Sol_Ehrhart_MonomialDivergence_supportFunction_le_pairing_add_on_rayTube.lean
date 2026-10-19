-- Prove2me | solution 1 for Ehrhart.MonomialDivergence.supportFunction_le_pairing_add_on_rayTube
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:10.440282+00:00
-- url     : https://prove2.me/submissions/72d61507-c8b8-4e41-89ab-ad01653f6018

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_MonomialDivergence_pairing_sub_left

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.MonomialDivergence
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace Ehrhart.MonomialDivergence
theorem _root_.solution {n : ℕ}
    {K : Set (Space n)} (hcompact : IsCompact K)
    (hnonempty : K.Nonempty)
    {u v : Space n}
    (hseparate : ∀ y ∈ K,
      SupportFunction.pairing y v ≤
        SupportFunction.pairing u v) :
    ∃ D : ℝ, ∀ x ∈ rayTube v,
      SupportFunction.supportFunction K x ≤
        SupportFunction.pairing u x + D := by
  obtain ⟨R, hR, hbound⟩ :=
    hcompact.isBounded.exists_pos_norm_le
  refine ⟨((n : ℝ) * (R + ‖u‖)) * (‖v‖ / 4),
    fun x hx => ?_⟩
  apply SupportFunction.supportFunction_le hnonempty x
  intro y hy
  have hx' : x ∈ ⋃ j : ℕ, rayBall v j := hx
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx'
  let w : Space n := x - (j : ℝ) • v
  have hw : ‖w‖ < ‖v‖ / 4 := by
    change ‖x - (j : ℝ) • v‖ < ‖v‖ / 4
    simpa [rayBall, dist_eq_norm] using hj
  have hdiff : ‖y - u‖ ≤ R + ‖u‖ := by
    calc
      ‖y - u‖ ≤ ‖y‖ + ‖u‖ := norm_sub_le y u
      _ ≤ R + ‖u‖ := add_le_add (hbound y hy) (le_refl ‖u‖)
  have hpairw :
      SupportFunction.pairing (y - u) w ≤
        ((n : ℝ) * (R + ‖u‖)) * (‖v‖ / 4) := by
    calc
      SupportFunction.pairing (y - u) w ≤
          |SupportFunction.pairing (y - u) w| :=
        le_abs_self _
      _ ≤ ((n : ℝ) * ‖y - u‖) * ‖w‖ :=
        abs_pairing_le_dimension_mul_norm (y - u) w
      _ ≤ ((n : ℝ) * (R + ‖u‖)) * ‖w‖ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hdiff (Nat.cast_nonneg n))
          (norm_nonneg w)
      _ ≤ ((n : ℝ) * (R + ‖u‖)) * (‖v‖ / 4) := by
        apply mul_le_mul_of_nonneg_left hw.le
        positivity
  have hvsep : SupportFunction.pairing (y - u) v ≤ 0 := by
    rw [pairing_sub_left]
    linarith [hseparate y hy]
  have hray :
      SupportFunction.pairing (y - u)
        ((j : ℝ) • v) ≤ 0 := by
    rw [pairing_smul_right]
    exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg j) hvsep
  have hsplit : x = w + (j : ℝ) • v := by
    exact (sub_add_cancel x ((j : ℝ) • v)).symm
  have htotal :
      SupportFunction.pairing (y - u) x ≤
        ((n : ℝ) * (R + ‖u‖)) * (‖v‖ / 4) := by
    rw [hsplit, pairing_add_right]
    linarith
  rw [pairing_sub_left] at htotal
  linarith
end Ehrhart.MonomialDivergence
