-- Prove2me | solution 1 for ExactKMeans.ProductReduction.coordinate_frame_orthonormal
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-15T19:20:14.402671+00:00
-- url     : https://prove2.me/submissions/7a7be72a-1705-497e-bfef-33caa2c53a09

import Definitions.Def_ExactKMeans_ProductReduction_Selector

open scoped BigOperators Classical
open Finset
open ExactKMeans.ProductReduction

namespace KMeansCoord

lemma inner_unit (d j k : ℕ) (hj : j < d) (_hk : k < d) :
    inner ℝ (unit d j) (unit d k) = if j = k then 1 else 0 := by
  unfold unit
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct]
  have hj' : ∀ x : Fin d, ((x : ℕ) = j) ↔ x = ⟨j, hj⟩ := fun x => by simp [Fin.ext_iff]
  simp [hj', Finset.sum_ite_eq']


section generic
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {b : ℕ}

abbrev ON (f : Fin b → V) : Prop := ∀ j k, inner ℝ (f j) (f k) = if j = k then (1 : ℝ) else 0
abbrev Perp (f : Fin b → V) (x : V) : Prop := ∀ j, inner ℝ (f j) x = 0

lemma norm_sq_frame {E P : Fin b → V}
    (hE : ∀ j k, inner ℝ (E j) (E k) = if j = k then (1 : ℝ) else 0)
    (hP : ∀ j k, inner ℝ (P j) (P k) = if j = k then (1 : ℝ) else 0)
    (hEP : ∀ j k, inner ℝ (E j) (P k) = 0) (x y : Fin b → ℝ) :
    ‖∑ j, (x j • E j + y j • P j)‖ ^ 2 = ∑ j, (x j ^ 2 + y j ^ 2) := by
  have hPE : ∀ j k, inner ℝ (P j) (E k) = 0 := fun j k => by rw [real_inner_comm, hEP]
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  refine sum_congr rfl fun j _ => ?_
  rw [inner_sum]
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, hE, hP, hEP, hPE,
    RCLike.conj_to_real, mul_ite, mul_one, mul_zero, add_zero, zero_add, ite_add_ite]
  simp [sum_ite_eq]
  ring

end generic

section concrete
variable (p : Parameters)

lemma d_eq : p.d = 2 * p.b + 1 := rfl

lemma e_on : ON (e p) := fun j k => by
  have hj := j.isLt; have hk := k.isLt
  show inner ℝ (unit p.d (2 * j.val)) (unit p.d (2 * k.val)) = _
  rw [inner_unit _ _ _ (by rw [d_eq]; omega) (by rw [d_eq]; omega)]
  have : (2 * j.val = 2 * k.val) ↔ j = k := by rw [Fin.ext_iff]; omega
  simp only [this]

lemma ep_on : ON (ep p) := fun j k => by
  have hj := j.isLt; have hk := k.isLt
  show inner ℝ (unit p.d (2 * j.val + 1)) (unit p.d (2 * k.val + 1)) = _
  rw [inner_unit _ _ _ (by rw [d_eq]; omega) (by rw [d_eq]; omega)]
  have : (2 * j.val + 1 = 2 * k.val + 1) ↔ j = k := by rw [Fin.ext_iff]; omega
  simp only [this]

lemma e_ep (j k : Fin p.b) : inner ℝ (e p j) (ep p k) = 0 := by
  have hj := j.isLt; have hk := k.isLt
  show inner ℝ (unit p.d (2 * j.val)) (unit p.d (2 * k.val + 1)) = _
  rw [inner_unit _ _ _ (by rw [d_eq]; omega) (by rw [d_eq]; omega)]
  rw [if_neg (by omega)]

lemma e_axis : Perp (e p) (axis p) := fun j => by
  have hj := j.isLt
  show inner ℝ (unit p.d (2 * j.val)) (unit p.d (2 * p.b)) = _
  rw [inner_unit _ _ _ (by rw [d_eq]; omega) (by rw [d_eq]; omega)]
  rw [if_neg (by omega)]

lemma ep_axis : Perp (ep p) (axis p) := fun j => by
  have hj := j.isLt
  show inner ℝ (unit p.d (2 * j.val + 1)) (unit p.d (2 * p.b)) = _
  rw [inner_unit _ _ _ (by rw [d_eq]; omega) (by rw [d_eq]; omega)]
  rw [if_neg (by omega)]

lemma axis_axis : inner ℝ (axis p) (axis p) = 1 := by
  show inner ℝ (unit p.d (2 * p.b)) (unit p.d (2 * p.b)) = _
  rw [inner_unit _ _ _ (by rw [d_eq]; omega) (by rw [d_eq]; omega)]
  simp

end concrete

end KMeansCoord

open KMeansCoord in
theorem solution (p : Parameters) :
    (∀ j k : Fin p.b, inner ℝ (e p j) (e p k) = if j = k then (1 : ℝ) else 0) ∧
    (∀ j k : Fin p.b, inner ℝ (ep p j) (ep p k) = if j = k then (1 : ℝ) else 0) ∧
    (∀ j k : Fin p.b, inner ℝ (e p j) (ep p k) = 0) ∧
    (∀ j : Fin p.b, inner ℝ (e p j) (axis p) = 0 ∧ inner ℝ (ep p j) (axis p) = 0) ∧
    inner ℝ (axis p) (axis p) = 1 ∧
    ∀ x y : Fin p.b → ℝ,
      ‖∑ j, (x j • e p j + y j • ep p j)‖ ^ 2 = ∑ j, (x j ^ 2 + y j ^ 2) := by
  exact ⟨e_on p, ep_on p, e_ep p, fun j => ⟨e_axis p j, ep_axis p j⟩, axis_axis p,
    norm_sq_frame (e_on p) (ep_on p) (e_ep p)⟩
