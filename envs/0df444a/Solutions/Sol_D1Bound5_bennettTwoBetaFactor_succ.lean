-- Prove2me | solution 1 for D1Bound5.bennettTwoBetaFactor_succ
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:34:14.863771+00:00
-- url     : https://prove2.me/submissions/cc440583-724a-4cca-b0ab-7bbf5afcf035

import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettTwoBetaBound_Definitions
import Theorems.Thm_D1Bound5_bennett_Gamma_add_two

section
namespace D1Bound5





theorem bennett_Gamma_add_three (x : ℝ) (hx : 0 < x) :
    Real.Gamma (x + 3) = (x + 2) * (x + 1) * x * Real.Gamma x := by
  rw [show x + 3 = (x + 2) + 1 by ring,
    Real.Gamma_add_one (show x + 2 ≠ 0 by linarith), bennett_Gamma_add_two x hx]
  ring





/-- The actual Gamma sequence obeys the rational recurrence used in the paper. -/
theorem _root_.solution (k : ℕ) (hk : 1 ≤ k) :
    bennettTwoBetaFactor (k + 1) = bennettTwoBetaFactor k *
      (((27 / 4 : ℝ) * ((k : ℝ) + 3 / 2) * (2 * (k : ℝ) - 1 / 2) *
        (2 * (k : ℝ) + 1 / 2)) /
          ((3 * (k : ℝ) + 1) * (3 * (k : ℝ) + 2) * (3 * (k : ℝ) + 3))) := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hg1 : Real.Gamma (((k + 1 : ℕ) : ℝ) + 3 / 2) =
      ((k : ℝ) + 3 / 2) * Real.Gamma ((k : ℝ) + 3 / 2) := by
    rw [show ((k + 1 : ℕ) : ℝ) + 3 / 2 = ((k : ℝ) + 3 / 2) + 1 by
      push_cast; ring]
    exact Real.Gamma_add_one (by linarith)
  have hg2 : Real.Gamma (2 * ((k + 1 : ℕ) : ℝ) - 1 / 2) =
      (2 * (k : ℝ) + 1 / 2) * (2 * (k : ℝ) - 1 / 2) *
        Real.Gamma (2 * (k : ℝ) - 1 / 2) := by
    rw [show 2 * ((k + 1 : ℕ) : ℝ) - 1 / 2 = (2 * (k : ℝ) - 1 / 2) + 2 by
      push_cast; ring, bennett_Gamma_add_two _ (by linarith)]
    ring
  have hg3 : Real.Gamma (3 * ((k + 1 : ℕ) : ℝ) + 1) =
      (3 * (k : ℝ) + 1) * (3 * (k : ℝ) + 2) * (3 * (k : ℝ) + 3) *
        Real.Gamma (3 * (k : ℝ) + 1) := by
    rw [show 3 * ((k + 1 : ℕ) : ℝ) + 1 = (3 * (k : ℝ) + 1) + 3 by
      push_cast; ring, bennett_Gamma_add_three _ (by positivity)]
    ring
  have hG : Real.Gamma (3 * (k : ℝ) + 1) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by positivity)).ne'
  have h1 : 3 * (k : ℝ) + 1 ≠ 0 := by positivity
  have h2 : 3 * (k : ℝ) + 2 ≠ 0 := by positivity
  have h3 : 3 * (k : ℝ) + 3 ≠ 0 := by positivity
  unfold bennettTwoBetaFactor
  rw [hg1, hg2, hg3, pow_succ]
  field_simp [Real.pi_ne_zero, hG, h1, h2, h3]
  <;> ring









end D1Bound5
end
