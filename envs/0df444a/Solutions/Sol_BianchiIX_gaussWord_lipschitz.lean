-- Prove2me | solution 1 for BianchiIX.gaussWord_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T13:09:05.621722+00:00
-- url     : https://prove2.me/submissions/c111e858-4db9-4361-bddd-f7c2df489a79

import Definitions.Def_BianchiIX_Statistics_GaussInverse
import Theorems.Thm_BianchiIX_gaussInv_pair_lipschitz
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.List.Induction
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open BianchiIX
noncomputable section
open Filter
open scoped Topology

private theorem BianchiIX.gaussInv_pos {a x : ℝ} (ha : 1 ≤ a) (hx : 0 ≤ x) : 0 < gaussInv a x := by
  unfold gaussInv
  exact one_div_pos.mpr (by linarith)

private theorem BianchiIX.gaussInv_lipschitz {a x y : ℝ} (ha : 1 ≤ a) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |gaussInv a x - gaussInv a y| ≤ |x - y| := by
  have hax : 0 < a + x := by linarith
  have hay : 0 < a + y := by linarith
  have hden : 1 ≤ (a + x) * (a + y) := by
    nlinarith [mul_nonneg (show 0 ≤ a + x - 1 by linarith)
      (show 0 ≤ a + y - 1 by linarith)]
  have hid : gaussInv a x - gaussInv a y = (y - x) / ((a + x) * (a + y)) := by
    unfold gaussInv
    field_simp
    ring
  rw [hid, abs_div, abs_of_pos (mul_pos hax hay), abs_sub_comm y x]
  exact div_le_self (abs_nonneg _) hden

private theorem BianchiIX.gaussWord_nonneg (w : List ℕ) (hw : ∀ a ∈ w, 1 ≤ a) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ gaussWord w x := by
  induction w with
  | nil => exact hx
  | cons a w ih =>
    have ha : (1 : ℝ) ≤ a := by exact_mod_cast hw a (by simp)
    exact (gaussInv_pos ha (ih (fun b hb => hw b (by simp [hb])))).le

theorem solution (w : List ℕ) (hw : ∀ a ∈ w, 1 ≤ a)
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |gaussWord w x - gaussWord w y| ≤ (1 / 4 : ℝ) ^ (w.length / 2) * |x - y| := by
  induction w using List.twoStepInduction with
  | nil => simp [gaussWord]
  | singleton a =>
    have ha : (1 : ℝ) ≤ a := by exact_mod_cast hw a (by simp)
    simpa [gaussWord] using gaussInv_lipschitz ha hx hy
  | cons_cons a b w ih _ =>
    have ha : (1 : ℝ) ≤ a := by exact_mod_cast hw a (by simp)
    have hb : (1 : ℝ) ≤ b := by exact_mod_cast hw b (by simp)
    have htail : ∀ c ∈ w, 1 ≤ c := fun c hc => hw c (by simp [hc])
    have hlen : (a :: b :: w).length / 2 = w.length / 2 + 1 := by
      simp [Nat.add_assoc, Nat.add_div_right]
    calc
      _ ≤ (1 / 4) * |gaussWord w x - gaussWord w y| :=
        gaussInv_pair_lipschitz ha hb (gaussWord_nonneg w htail hx) (gaussWord_nonneg w htail hy)
      _ ≤ (1 / 4) * ((1 / 4) ^ (w.length / 2) * |x - y|) :=
        mul_le_mul_of_nonneg_left (ih htail) (by norm_num)
      _ = _ := by rw [hlen, pow_succ]; ring
