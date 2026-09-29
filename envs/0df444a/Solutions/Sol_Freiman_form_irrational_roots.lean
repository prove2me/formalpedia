-- Prove2me | solution 1 for Freiman.form_irrational_roots
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T20:08:33.690691+00:00
-- url     : https://prove2.me/submissions/116ffb05-7cbd-4af2-9cde-f5246356428e

import Definitions.Def_Freiman_reducedForms
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false
set_option maxHeartbeats 800000

open Freiman

theorem solution (A B C : ℝ) (hd : 0 < B^2-4*A*C)
    (hm : 0 < quadraticMinimum A B C) :
    A ≠ 0 ∧ ∃ r s : ℝ, s < r ∧ Irrational r ∧ Irrational s ∧
      ∀ p q : ℤ, quadraticValue A B C p q =
        A * ((p:ℝ)-r*(q:ℝ)) * ((p:ℝ)-s*(q:ℝ)) := by
  have hnonzero (p q : ℤ) (hpq : p ≠ 0 ∨ q ≠ 0) :
      quadraticValue A B C p q ≠ 0 := by
    intro hz
    have hb : BddBelow {v : ℝ | ∃ p q : ℤ,
        (p ≠ 0 ∨ q ≠ 0) ∧ v = |quadraticValue A B C p q|} := by
      refine ⟨0, ?_⟩
      rintro v ⟨p, q, hpq, rfl⟩
      exact abs_nonneg _
    have hmle : quadraticMinimum A B C ≤ |quadraticValue A B C p q| :=
      csInf_le hb ⟨p, q, hpq, rfl⟩
    rw [hz, abs_zero] at hmle
    linarith
  have hA : A ≠ 0 := by
    intro hz
    exact hnonzero 1 0 (Or.inl one_ne_zero) (by simp [quadraticValue, hz])
  let x : ℝ := (-B + Real.sqrt (B^2-4*A*C)) / (2*A)
  let y : ℝ := (-B - Real.sqrt (B^2-4*A*C)) / (2*A)
  have hsqrt : (Real.sqrt (B^2-4*A*C))^2 = B^2-4*A*C :=
    Real.sq_sqrt hd.le
  have hsqrtpos : 0 < Real.sqrt (B^2-4*A*C) := Real.sqrt_pos.2 hd
  have hsum : A*(x+y) = -B := by
    dsimp [x, y]
    field_simp
    <;> ring
  have hprod : A*x*y = C := by
    dsimp [x, y]
    field_simp
    <;> nlinarith [Real.sq_sqrt (show 0 ≤ B^2-A*4*C by nlinarith)]
  have hfactor (p q : ℤ) : quadraticValue A B C p q =
      A * ((p:ℝ)-x*(q:ℝ)) * ((p:ℝ)-y*(q:ℝ)) := by
    calc
      quadraticValue A B C p q = A*(p:ℝ)^2 + B*(p:ℝ)*(q:ℝ) + C*(q:ℝ)^2 := rfl
      _ = A*(p:ℝ)^2 - (A*(x+y))*(p:ℝ)*(q:ℝ) + (A*x*y)*(q:ℝ)^2 := by
        rw [hsum, hprod]
        ring
      _ = _ := by ring
  have hix : Irrational x := by
    rw [irrational_iff_ne_rational]
    intro p q hq heq
    have hq' : (q:ℝ) ≠ 0 := Int.cast_ne_zero.mpr hq
    apply hnonzero p q (Or.inr hq)
    rw [hfactor, heq]
    field_simp
    ring
  have hiy : Irrational y := by
    rw [irrational_iff_ne_rational]
    intro p q hq heq
    have hq' : (q:ℝ) ≠ 0 := Int.cast_ne_zero.mpr hq
    apply hnonzero p q (Or.inr hq)
    rw [hfactor, heq]
    field_simp
    ring
  have hxy : x ≠ y := by
    intro heq
    have hden : 2*A ≠ 0 := mul_ne_zero (by norm_num) hA
    have heq' := (div_left_inj' hden).mp heq
    linarith
  refine ⟨hA, ?_⟩
  rcases lt_or_gt_of_ne hxy with hlt | hgt
  · refine ⟨y, x, hlt, hiy, hix, ?_⟩
    intro p q
    rw [hfactor]
    ring
  · exact ⟨x, y, hgt, hix, hiy, hfactor⟩
