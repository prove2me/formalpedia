-- Prove2me | solution 1 for BianchiIX.gaussInv_pair_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T13:06:11.065055+00:00
-- url     : https://prove2.me/submissions/675934e7-9e31-472d-b7b1-1c5ed4bac9dd

import Definitions.Def_BianchiIX_Statistics_GaussInverse
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

private theorem BianchiIX.gaussInv_pair_eq {a b x : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hx : 0 ≤ x) :
    gaussInv a (gaussInv b x) = (b + x) / (a * (b + x) + 1) := by
  have hbpos : 0 < b + x := by linarith
  have hapos : 0 < a + 1 / (b + x) := by positivity
  have hprod : 0 < a * (b + x) + 1 := by positivity
  unfold gaussInv
  field_simp

theorem solution
    {a b x y : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |gaussInv a (gaussInv b x) - gaussInv a (gaussInv b y)| ≤ (1 / 4) * |x - y| := by
  have hdx : 2 ≤ a * (b + x) + 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ha) (show 0 ≤ b + x by linarith)]
  have hdy : 2 ≤ a * (b + y) + 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ha) (show 0 ≤ b + y by linarith)]
  have hdxpos : 0 < a * (b + x) + 1 := by linarith
  have hdypos : 0 < a * (b + y) + 1 := by linarith
  have hden : 4 ≤ (a * (b + x) + 1) * (a * (b + y) + 1) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hdx) (sub_nonneg.mpr hdy)]
  rw [gaussInv_pair_eq ha hb hx, gaussInv_pair_eq ha hb hy]
  have hid : (b + x) / (a * (b + x) + 1) - (b + y) / (a * (b + y) + 1) =
      (x - y) / ((a * (b + x) + 1) * (a * (b + y) + 1)) := by
    field_simp
    ring
  rw [hid, abs_div, abs_of_pos (mul_pos hdxpos hdypos)]
  calc
    _ ≤ |x - y| / 4 := div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num) hden
    _ = (1 / 4) * |x - y| := by ring
