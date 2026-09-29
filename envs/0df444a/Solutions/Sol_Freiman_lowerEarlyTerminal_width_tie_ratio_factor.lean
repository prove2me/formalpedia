-- Prove2me | solution 1 for Freiman.lowerEarlyTerminal_width_tie_ratio_factor
-- status  : ACCEPTED   (prove)
-- author  : @Marac
-- created : 2026-09-12T04:06:56.975317+00:00
-- url     : https://prove2.me/submissions/597fd6de-0621-4c76-b06f-e560614c72df

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

open Freiman

theorem cd_eq (w : List ℕ+) : lowerCD w =
    List.foldl (fun z (a : ℕ) => (z.2, z.1 + a * z.2)) (0, 1) (w.map PNat.val) := by
  have hbind : (do let a ← w; pure (a : ℕ)) = w.map PNat.val := by
    induction w with
    | nil => rfl
    | cons a w ih => simpa using ih
  unfold lowerCD
  rw [hbind]

theorem cd_append (w : List ℕ+) (a : ℕ+) :
    lowerCD (w ++ [a]) = ((lowerCD w).2, (lowerCD w).1 + (a : ℕ) * (lowerCD w).2) := by
  rw [cd_eq, cd_eq, List.map_append, List.foldl_append]
  simp

theorem cd_pos : ∀ w : List ℕ+, 0 < (lowerCD w).2 := by
  intro w
  induction w using List.reverseRecOn with
  | nil => rw [cd_eq]; norm_num
  | append_singleton w a ih =>
      rw [cd_append]
      show 0 < (lowerCD w).1 + (a : ℕ) * (lowerCD w).2
      have h1 : 0 < (a : ℕ) * (lowerCD w).2 := Nat.mul_pos a.pos ih
      omega

theorem solution (u v : List ℕ+) (h : (((lowerCD u).1:ℤ)^2+((lowerCD u).2:ℤ)^2 =
        ((lowerCD v).1:ℤ)^2+((lowerCD v).2:ℤ)^2) ∧
      (4*((lowerCD u).1:ℤ)*(lowerCD u).2-3*((lowerCD u).1:ℤ)^2 =
        4*((lowerCD v).1:ℤ)*(lowerCD v).2-3*((lowerCD v).1:ℤ)^2)) : lowerRatio u = lowerRatio v ∨
      lowerRatio v = (4-3*lowerRatio u)/(3+4*lowerRatio u) := by
  obtain ⟨h1z, h2z⟩ := h
  set cu : ℝ := ((lowerCD u).1 : ℝ) with hcu
  set du : ℝ := ((lowerCD u).2 : ℝ) with hdu
  set cv : ℝ := ((lowerCD v).1 : ℝ) with hcv
  set dv : ℝ := ((lowerCD v).2 : ℝ) with hdv
  have h1 : cu^2 + du^2 = cv^2 + dv^2 := by simp only [hcu, hdu, hcv, hdv]; exact_mod_cast h1z
  have h2 : 4*cu*du - 3*cu^2 = 4*cv*dv - 3*cv^2 := by simp only [hcu, hdu, hcv, hdv]; exact_mod_cast h2z
  have pdu : 0 < du := by simp only [hdu]; exact_mod_cast cd_pos u
  have pdv : 0 < dv := by simp only [hdv]; exact_mod_cast cd_pos v
  have pcu : 0 ≤ cu := Nat.cast_nonneg _
  have key : (cv*du - cu*dv) * (3*cv*du + 4*cu*cv - 4*du*dv + 3*cu*dv) = 0 := by
    linear_combination (3*cu^2 - 4*cu*du) * h1 + (cu^2 + du^2) * h2
  have ru : lowerRatio u = cu/du := rfl
  have rv : lowerRatio v = cv/dv := rfl
  rw [ru, rv]
  rcases mul_eq_zero.1 key with h0 | h0
  · left
    rw [div_eq_div_iff pdu.ne' pdv.ne']
    linarith
  · right
    have hpos : (0:ℝ) < 3 + 4*(cu/du) := by
      have : 0 ≤ cu/du := div_nonneg pcu pdu.le
      linarith
    rw [div_eq_div_iff pdv.ne' hpos.ne']
    apply mul_right_cancel₀ pdu.ne'
    have hx : cu/du*du = cu := div_mul_cancel₀ cu pdu.ne'
    linear_combination h0 + (4*cv + 3*dv) * hx
