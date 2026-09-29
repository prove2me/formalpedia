-- Prove2me | solution 2 for Freiman.lowerEarlyTerminal_width_tie_ratios
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-12T00:27:29.988618+00:00
-- url     : https://prove2.me/submissions/890e6604-d795-4afb-aecc-11173d77b23d

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry
import Theorems.Thm_Freiman_lowerJ_width_formula
import Theorems.Thm_Freiman_lowerEarlyTerminal_width_tie_coefficients
import Mathlib.Tactic

open Freiman

private theorem cd_bounds : ∀ (w : List ℕ+) (z : ℕ × ℕ), z.1 ≤ z.2 → 1 ≤ z.2 →
    (w.foldl (fun z a => (z.2, z.1 + (a : ℕ) * z.2)) z).1
        ≤ (w.foldl (fun z a => (z.2, z.1 + (a : ℕ) * z.2)) z).2 ∧
      1 ≤ (w.foldl (fun z a => (z.2, z.1 + (a : ℕ) * z.2)) z).2 := by
  intro w
  induction w with
  | nil => intro z h1 h2; exact ⟨h1, h2⟩
  | cons a t ih =>
    intro z h1 h2
    have ha : 1 ≤ (a : ℕ) := a.property
    have key : z.2 ≤ (a:ℕ) * z.2 := by
      calc z.2 = 1 * z.2 := by ring
        _ ≤ (a:ℕ) * z.2 := Nat.mul_le_mul_right _ ha
    refine ih _ ?_ ?_ <;> simp only <;> omega

private theorem cd_posR (w : List ℕ+) : (0:ℝ) < ((lowerCD w).2 : ℝ) := by
  have h : 1 ≤ (lowerCD w).2 := by
    unfold lowerCD; exact (cd_bounds w (0,1) (by norm_num) (by norm_num)).2
  exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one h

theorem solution (u v : List ℕ+) (h : lowerWidth u = lowerWidth v) :
    lowerRatio u = lowerRatio v ∨
      lowerRatio v = (4-3*lowerRatio u)/(3+4*lowerRatio u) := by
  obtain ⟨h1, h2⟩ := Freiman.lowerEarlyTerminal_width_tie_coefficients
    Freiman.lowerJ_width_formula u v h
  have hBR := cd_posR u
  have hDR := cd_posR v
  have hr0 : 0 ≤ lowerRatio u := by unfold lowerRatio; positivity
  -- the two integer invariants factor
  have key : (((lowerCD u).1:ℤ) * ((lowerCD v).2:ℤ) - ((lowerCD v).1:ℤ) * ((lowerCD u).2:ℤ))
      * (4*((lowerCD u).2:ℤ)*((lowerCD v).2:ℤ) - 3*((lowerCD u).1:ℤ)*((lowerCD v).2:ℤ)
          - 3*((lowerCD v).1:ℤ)*((lowerCD u).2:ℤ) - 4*((lowerCD u).1:ℤ)*((lowerCD v).1:ℤ)) = 0 := by
    linear_combination (-(4*((lowerCD u).1:ℤ)*((lowerCD u).2:ℤ)-3*((lowerCD u).1:ℤ)^2)) * h1
      + (((lowerCD u).1:ℤ)^2+((lowerCD u).2:ℤ)^2) * h2
  rcases mul_eq_zero.mp key with hc | hc
  · left
    unfold lowerRatio
    rw [div_eq_div_iff hBR.ne' hDR.ne']
    have : ((lowerCD u).1:ℤ) * ((lowerCD v).2:ℤ) = ((lowerCD v).1:ℤ) * ((lowerCD u).2:ℤ) := by
      linarith [hc]
    exact_mod_cast this
  · right
    have hz : 4*((lowerCD u).2:ℝ)*((lowerCD v).2:ℝ) - 3*((lowerCD u).1:ℝ)*((lowerCD v).2:ℝ)
        - 3*((lowerCD v).1:ℝ)*((lowerCD u).2:ℝ) - 4*((lowerCD u).1:ℝ)*((lowerCD v).1:ℝ) = 0 := by
      exact_mod_cast hc
    unfold lowerRatio
    rw [eq_div_iff (by positivity)]
    field_simp at hz ⊢
    linarith [hz]
