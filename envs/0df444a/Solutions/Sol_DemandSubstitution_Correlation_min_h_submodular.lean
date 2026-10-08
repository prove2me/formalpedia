-- Prove2me | solution 1 for DemandSubstitution.Correlation.min_h_submodular
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T08:51:56.74889+00:00
-- url     : https://prove2.me/submissions/d04713e8-4068-40d7-a808-85c2bc425071

import Mathlib
import Definitions.Def_Supermodularity_Monotonicity_SupermodularOn
import Definitions.Def_DemandSubstitution_Correlation_Setting

open DemandSubstitution.Correlation Supermodularity.Monotonicity

private theorem ds_valuation {n : ℕ} (M : Model n) (Q x y : Fin n → ℝ) (i : Fin n) :
    Ds M Q x i + Ds M Q y i = Ds M Q (x ⊔ y) i + Ds M Q (x ⊓ y) i := by
  classical
  have hc (j : Fin n) :
      M.a j i * max (x j - Q j) 0 + M.a j i * max (y j - Q j) 0 =
        M.a j i * max ((x ⊔ y) j - Q j) 0 +
          M.a j i * max ((x ⊓ y) j - Q j) 0 := by
    change _ = M.a j i * max (max (x j) (y j) - Q j) 0 +
      M.a j i * max (min (x j) (y j) - Q j) 0
    rcases le_total (x j) (y j) with h | h
    · rw [max_eq_right h, min_eq_left h]; ring
    · rw [max_eq_left h, min_eq_right h]
  have hi : x i + y i = (x ⊔ y) i + (x ⊓ y) i := by
    exact (max_add_min (x i) (y i)).symm
  unfold Ds
  have hs := Finset.sum_congr (s₁ := Finset.univ.erase i) rfl (fun j _ => hc j)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hs
  linarith


private theorem ds_mono {n : ℕ} (M : Model n) (Q : Fin n → ℝ) (i : Fin n) :
    Monotone (fun x => Ds M Q x i) := by
  classical
  intro x y h
  apply add_le_add (h i)
  apply Finset.sum_le_sum
  intro j hj
  exact mul_le_mul_of_nonneg_left
    (max_le_max (sub_le_sub_right (h j) _) le_rfl) (M.a_nonneg j i)

theorem solution {n : ℕ} (M : Model n) (Q : Fin n → ℝ) (hQ : ∀ k, 0 ≤ Q k)
    (i : Fin n) :
    SupermodularOn (fun x => -(min (Ds M Q x i) (Q i))) Set.univ := by
  intro x hx y hy
  dsimp only
  have hv := ds_valuation M Q x y i
  have hxlo := ds_mono M Q i (inf_le_left : x ⊓ y ≤ x)
  have hylo := ds_mono M Q i (inf_le_right : x ⊓ y ≤ y)
  have hxhi := ds_mono M Q i (le_sup_left : x ≤ x ⊔ y)
  have hyhi := ds_mono M Q i (le_sup_right : y ≤ x ⊔ y)
  rcases le_total (Ds M Q x i) (Q i) with hxc | hcx <;>
    rcases le_total (Ds M Q y i) (Q i) with hyc | hcy
  · rw [min_eq_left hxc, min_eq_left hyc, min_eq_left (hxlo.trans hxc)]
    have hh := min_le_left (Ds M Q (x ⊔ y) i) (Q i)
    linarith
  · rw [min_eq_left hxc, min_eq_right hcy,
      min_eq_left (hxlo.trans hxc), min_eq_right (hcy.trans hyhi)]
    linarith
  · rw [min_eq_right hcx, min_eq_left hyc,
      min_eq_left (hylo.trans hyc), min_eq_right (hcx.trans hxhi)]
    linarith
  · rw [min_eq_right hcx, min_eq_right hcy,
      min_eq_right (hcx.trans hxhi)]
    have hh := min_le_right (Ds M Q (x ⊓ y) i) (Q i)
    linarith

#print axioms solution
