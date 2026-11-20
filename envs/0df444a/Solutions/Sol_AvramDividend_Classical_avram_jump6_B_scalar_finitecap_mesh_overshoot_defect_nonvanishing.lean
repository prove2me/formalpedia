-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_scalar_finitecap_mesh_overshoot_defect_nonvanishing
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T22:06:36.837726+00:00
-- url     : https://prove2.me/submissions/ecca5213-9147-443f-affb-7963b972cf54

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
noncomputable section
set_option autoImplicit false

theorem solution
    (m : ℕ) (hm : 0 < m) :
    let a : ℝ := 1 / (m : ℝ)
    let w : ℝ → ℝ := fun y => if y ≤ 1 then y else 2 - y
    let V : ℝ → ℝ := id
    (m : ℝ) * (V (1 + a) - w (1 + a)) = 2 := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hmne : (m : ℝ) ≠ 0 := ne_of_gt hmpos
  have hlt : (1 : ℝ) < 1 + 1 / (m : ℝ) := by
    have hh : (0 : ℝ) < 1 / (m : ℝ) := by positivity
    linarith
  dsimp
  rw [if_neg (not_le.mpr hlt)]
  field_simp
  ring