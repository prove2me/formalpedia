-- Prove2me | solution 1 for Freiman.lowerEarlyTerminal_width_tie_coefficients
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-11T21:05:26.597775+00:00
-- url     : https://prove2.me/submissions/173c1837-262c-48ea-bca3-f2d672567c51

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry
import Mathlib.Tactic
import Mathlib.NumberTheory.Real.Irrational

open Freiman

private theorem fold_den : ∀ (w : List ℕ+) (z : ℕ × ℕ), 1 ≤ z.2 →
    1 ≤ (w.foldl (fun z a => (z.2, z.1 + (a : ℕ) * z.2)) z).2 := by
  intro w
  induction w with
  | nil => intro z hz; exact hz
  | cons a t ih =>
    intro z hz
    refine ih _ ?_
    have ha : 1 ≤ (a : ℕ) := a.property
    calc (1:ℕ) = 1 * 1 := by norm_num
      _ ≤ (a:ℕ) * z.2 := Nat.mul_le_mul ha hz
      _ ≤ z.1 + (a:ℕ) * z.2 := Nat.le_add_left _ _

private theorem cd_den (w : List ℕ+) : 1 ≤ (lowerCD w).2 := by
  unfold lowerCD
  exact fold_den w (0,1) le_rfl

private theorem sqrt21_key (a b : ℤ) (hab : (a:ℝ) + (b:ℝ) * Real.sqrt 21 = 0) :
    a = 0 ∧ b = 0 := by
  have h21 : Irrational (Real.sqrt 21) := by norm_num
  by_cases hb : b = 0
  · subst hb
    norm_num at hab
    exact ⟨by exact_mod_cast hab, rfl⟩
  · exfalso
    have hb' : (b:ℝ) ≠ 0 := Int.cast_ne_zero.mpr hb
    refine h21 ⟨(-a : ℚ)/(b : ℚ), ?_⟩
    push_cast
    field_simp
    linarith

set_option maxHeartbeats 1000000 in
theorem solution (hw : ∀ w : List ℕ+, lowerWidth w = (lowerBeta-lowerAlpha)/
      ((((lowerCD w).1:ℝ)*lowerAlpha+(lowerCD w).2)*(((lowerCD w).1:ℝ)*lowerBeta+(lowerCD w).2))) (u v : List ℕ+)
    (h : lowerWidth u = lowerWidth v) : (((lowerCD u).1:ℤ)^2+((lowerCD u).2:ℤ)^2 =
        ((lowerCD v).1:ℤ)^2+((lowerCD v).2:ℤ)^2) ∧
      (4*((lowerCD u).1:ℤ)*(lowerCD u).2-3*((lowerCD u).1:ℤ)^2 =
        4*((lowerCD v).1:ℤ)*(lowerCD v).2-3*((lowerCD v).1:ℤ)^2) := by
  have hs : Real.sqrt 21 ^ 2 = 21 := Real.sq_sqrt (by norm_num)
  have hs0 : (0:ℝ) < Real.sqrt 21 := Real.sqrt_pos.mpr (by norm_num)
  have hs4 : (4:ℝ) < Real.sqrt 21 := by nlinarith [hs, hs0]
  have ha0 : (0:ℝ) < lowerAlpha := by
    unfold lowerAlpha; linarith
  have hb0 : (0:ℝ) < lowerBeta := by
    unfold lowerBeta; linarith
  -- every denominator factor is at least one
  have hfac : ∀ w : List ℕ+,
      (1:ℝ) ≤ (((lowerCD w).1:ℝ)*lowerAlpha+((lowerCD w).2:ℝ)) ∧
      (1:ℝ) ≤ (((lowerCD w).1:ℝ)*lowerBeta+((lowerCD w).2:ℝ)) := by
    intro w
    have hd : (1:ℝ) ≤ ((lowerCD w).2 : ℝ) := by exact_mod_cast cd_den w
    have hc : (0:ℝ) ≤ ((lowerCD w).1 : ℝ) := by positivity
    constructor
    · nlinarith [mul_nonneg hc ha0.le]
    · nlinarith [mul_nonneg hc hb0.le]
  have hDpos : ∀ w : List ℕ+, (0:ℝ) <
      ((((lowerCD w).1:ℝ)*lowerAlpha+((lowerCD w).2:ℝ))*(((lowerCD w).1:ℝ)*lowerBeta+((lowerCD w).2:ℝ))) := by
    intro w
    obtain ⟨h1, h2⟩ := hfac w
    nlinarith
  have hba : lowerBeta - lowerAlpha ≠ 0 := by
    unfold lowerAlpha lowerBeta; intro hc; nlinarith [hs4]
  rw [hw u, hw v, div_eq_div_iff (hDpos u).ne' (hDpos v).ne'] at h
  have hD : (((lowerCD u).1:ℝ)*lowerAlpha+((lowerCD u).2:ℝ))*(((lowerCD u).1:ℝ)*lowerBeta+((lowerCD u).2:ℝ))
      = (((lowerCD v).1:ℝ)*lowerAlpha+((lowerCD v).2:ℝ))*(((lowerCD v).1:ℝ)*lowerBeta+((lowerCD v).2:ℝ)) :=
    (mul_left_cancel₀ hba h).symm
  -- the rational and √21 parts of the denominator quadratic
  set cu : ℤ := ((lowerCD u).1 : ℤ) with hcu
  set du : ℤ := ((lowerCD u).2 : ℤ) with hdu
  set cv : ℤ := ((lowerCD v).1 : ℤ) with hcv
  set dv : ℤ := ((lowerCD v).2 : ℤ) with hdv
  have hcomb : ((15*(cu^2-cv^2) - 12*(cu*du-cv*dv) + 6*(du^2-dv^2) : ℤ) : ℝ)
      + ((-3*(cu^2-cv^2) + 4*(cu*du-cv*dv) : ℤ) : ℝ) * Real.sqrt 21 = 0 := by
    unfold lowerAlpha lowerBeta at hD
    push_cast [hcu, hdu, hcv, hdv]
    linear_combination 6*hD - (((((lowerCD u).1 : ℝ))^2 - (((lowerCD v).1 : ℝ))^2)/2) * hs
  obtain ⟨hP, hQ⟩ := sqrt21_key _ _ hcomb
  constructor
  · linarith [hP, hQ]
  · linarith [hQ]
