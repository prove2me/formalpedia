-- Prove2me | solution 1 for ChoiceCDLP.MNL.relaxedObjective_quasiconvexOn
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T07:45:18.92217+00:00
-- url     : https://prove2.me/submissions/c04090bb-8692-434f-9fc2-ac74abaf665b

import Mathlib
import Definitions.Def_ChoiceCDLP_MNL_relaxedObjective

namespace Aux_CDLP_QC
open ChoiceCDLP.MNL

variable {ι : Type*} [Fintype ι]

def N (w : ι → ℝ) (z : ι → ℝ) : ℝ := ∑ j, w j * z j
def D (v₀ : ℝ) (z : ι → ℝ) : ℝ := ∑ j, z j + v₀

lemma obj_eq (w : ι → ℝ) (v₀ : ℝ) (z : ι → ℝ) :
    relaxedObjective w v₀ z = N w z / D v₀ z := rfl

lemma D_nonneg (v : ι → ℝ) (v₀ : ℝ) (hv₀ : 0 ≤ v₀) (z : ι → ℝ) (hz : z ∈ Set.Icc 0 v) :
    0 ≤ D v₀ z := by
  have hz0 : ∀ j, 0 ≤ z j := fun j => hz.1 j
  unfold D
  have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => hz0 j)
  linarith

lemma N_zero (w v : ι → ℝ) (v₀ : ℝ) (hv₀ : 0 ≤ v₀) (z : ι → ℝ) (hz : z ∈ Set.Icc 0 v)
    (hD : D v₀ z = 0) : N w z = 0 := by
  have hz0 : ∀ j, 0 ≤ z j := fun j => hz.1 j
  have hs0 : 0 ≤ ∑ j, z j := Finset.sum_nonneg (fun j _ => hz0 j)
  unfold D at hD
  have hs : ∑ j, z j = 0 := by linarith
  have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hz0 j)).mp hs
  unfold N
  exact Finset.sum_eq_zero (fun j hj => by rw [hall j hj, mul_zero])

lemma bound (w v : ι → ℝ) (v₀ : ℝ) (hv₀ : 0 ≤ v₀) (z : ι → ℝ) (hz : z ∈ Set.Icc 0 v)
    (m : ℝ) (h : relaxedObjective w v₀ z ≤ m) : N w z ≤ m * D v₀ z := by
  by_cases hD : D v₀ z = 0
  · rw [N_zero w v v₀ hv₀ z hz hD, hD, mul_zero]
  · have hpos : 0 < D v₀ z := lt_of_le_of_ne (D_nonneg v v₀ hv₀ z hz) (Ne.symm hD)
    rw [obj_eq] at h
    exact (div_le_iff₀ hpos).mp h

end Aux_CDLP_QC

open ChoiceCDLP.MNL Aux_CDLP_QC in
theorem solution {ι : Type*} [Fintype ι] (v w : ι → ℝ) (v₀ : ℝ)
    (hv : ∀ j, 0 < v j) (hv₀ : 0 ≤ v₀) :
    QuasiconvexOn ℝ (Set.Icc 0 v) (relaxedObjective w v₀) := by
  rw [quasiconvexOn_iff_le_max]
  refine ⟨convex_Icc 0 v, fun x hx y hy a b ha hb hab => ?_⟩
  have hNc : N w (a • x + b • y) = a * N w x + b * N w y := by
    unfold N
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hDc : D v₀ (a • x + b • y) = a * D v₀ x + b * D v₀ y := by
    unfold D
    have hsum : ∑ j, (a • x + b • y) j = a * ∑ j, x j + b * ∑ j, y j := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun j _ => rfl)
    rw [hsum]
    have hv₀' : v₀ = (a + b) * v₀ := by rw [hab, one_mul]
    linarith
  have hDx0 := D_nonneg v v₀ hv₀ x hx
  have hDy0 := D_nonneg v v₀ hv₀ y hy
  rw [obj_eq w v₀ (a • x + b • y)]
  by_cases hDc0 : D v₀ (a • x + b • y) = 0
  · rw [hDc0, div_zero]
    have hsum : a * D v₀ x + b * D v₀ y = 0 := by rw [← hDc]; exact hDc0
    rcases eq_or_lt_of_le ha with h | h
    · have hb1 : b = 1 := by linarith
      rw [← h, hb1] at hsum
      have hDy : D v₀ y = 0 := by linarith
      have hfy : relaxedObjective w v₀ y = 0 := by rw [obj_eq, hDy, div_zero]
      exact le_max_of_le_right hfy.ge
    · have h1 : a * D v₀ x = 0 := by
        nlinarith [mul_nonneg ha hDx0, mul_nonneg hb hDy0]
      have hDx : D v₀ x = 0 := (mul_eq_zero.mp h1).resolve_left h.ne'
      have hfx : relaxedObjective w v₀ x = 0 := by rw [obj_eq, hDx, div_zero]
      exact le_max_of_le_left hfx.ge
  · have hpos : 0 < D v₀ (a • x + b • y) := by
      rcases lt_or_eq_of_le (show 0 ≤ D v₀ (a • x + b • y) by
        rw [hDc]; nlinarith [mul_nonneg ha hDx0, mul_nonneg hb hDy0]) with h | h
      · exact h
      · exact absurd h.symm hDc0
    rw [div_le_iff₀ hpos, hNc, hDc]
    have bx := bound w v v₀ hv₀ x hx _ (le_max_left (relaxedObjective w v₀ x)
      (relaxedObjective w v₀ y))
    have byy := bound w v v₀ hv₀ y hy _ (le_max_right (relaxedObjective w v₀ x)
      (relaxedObjective w v₀ y))
    nlinarith [mul_le_mul_of_nonneg_left bx ha, mul_le_mul_of_nonneg_left byy hb]
