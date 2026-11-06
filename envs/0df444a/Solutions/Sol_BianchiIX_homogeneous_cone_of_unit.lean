-- Prove2me | solution 1 for BianchiIX.homogeneous_cone_of_unit
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T06:55:06.09063+00:00
-- url     : https://prove2.me/submissions/6737513b-0da8-4a08-86a7-4c020defe59f

import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX


/-- Unit-phase estimates extend to both orientations and to the vertex of a linear cone. -/
theorem solution
    (D : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ)) {R a b A B : ℝ} (hR : 0 < R)
    (hunit : ∀ z : Fin 3 → ℝ, R * z 0 = 1 → |z 1| ≤ a → |z 2| ≤ b →
      0 ≤ D z 0 ∧ |D z 1| ≤ A * D z 0 ∧ |D z 2| ≤ B * D z 0)
    (v : Fin 3 → ℝ) (hva : |v 1| ≤ a * |R * v 0|) (hvb : |v 2| ≤ b * |R * v 0|) :
    |D v 1| ≤ A * |D v 0| ∧ |D v 2| ≤ B * |D v 0| := by
  let c := R * v 0
  by_cases hc : c = 0
  · have hv0 : v 0 = 0 := (mul_eq_zero.mp hc).resolve_left (ne_of_gt hR)
    have hv1 : v 1 = 0 := by
      change |v 1| ≤ a * |c| at hva
      simpa only [hc, abs_zero, mul_zero, abs_nonpos_iff] using hva
    have hv2 : v 2 = 0 := by
      change |v 2| ≤ b * |c| at hvb
      simpa only [hc, abs_zero, mul_zero, abs_nonpos_iff] using hvb
    have hv : v = 0 := by ext i; fin_cases i <;> assumption
    rw [hv, map_zero]
    simp
  · let z := c⁻¹ • v
    have hz0 : R * z 0 = 1 := by
      change R * (c⁻¹ * v 0) = 1
      calc
        _ = c⁻¹ * c := by dsimp only [c]; ring
        _ = 1 := inv_mul_cancel₀ hc
    have hz (i : Fin 3) (s : ℝ) (hi : |v i| ≤ s * |c|) : |z i| ≤ s := by
      change |c⁻¹ * v i| ≤ s
      rw [abs_mul, abs_inv]
      calc
        _ ≤ |c|⁻¹ * (s * |c|) := mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr (abs_nonneg _))
        _ = s := by field_simp
    have H := hunit z hz0 (hz 1 a hva) (hz 2 b hvb)
    have hv : v = c • z := by dsimp only [z]; rw [smul_smul, mul_inv_cancel₀ hc, one_smul]
    have hd (i : Fin 3) : |D v i| = |c| * |D z i| := by rw [hv, map_smul]; exact abs_mul c (D z i)
    have hd0 : |D v 0| = |c| * D z 0 := by rw [hd, abs_of_nonneg H.1]
    constructor
    · rw [hd, hd0]
      exact (mul_le_mul_of_nonneg_left H.2.1 (abs_nonneg c)).trans_eq (by ring)
    · rw [hd, hd0]
      exact (mul_le_mul_of_nonneg_left H.2.2 (abs_nonneg c)).trans_eq (by ring)
