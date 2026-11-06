-- Prove2me | solution 1 for BianchiIX.connection_phase_radial_budget
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T06:55:33.46676+00:00
-- url     : https://prove2.me/submissions/52d57a41-c049-4391-8a97-86a7f82ed4e5

import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.GCongr

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX


/-- Ordinary connection columns retain the full strong amplitude and the squared weak amplitude. -/
theorem solution {r K M A B μ U P u w v0 v1 v2 : ℝ}
    (hr : 0 < r) (hK : 0 ≤ K) (hM : 0 ≤ M) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hμ : 0 < μ) (hi : 1 / μ ≤ K * r) (hU : 0 ≤ U) (hP : 0 ≤ P ∧ P ≤ 1)
    (hu : 0 ≤ u ∧ u ≤ U) (hw : 0 ≤ w ∧ w ≤ P)
    (hv0 : |v0| ≤ M / r ^ 2) (hv1 : r * |v1| ≤ A * U) (hv2 : r * |v2| ≤ B * P) :
    |v0| * (50000 * (u + w ^ 2) / μ ^ 2) + |v1| * (50000 / μ) +
      |v2| * (50000 * (u + w) / μ) ≤
        50000 * (K ^ 2 * M + K * A + K * B) * (U + P ^ 2) := by
  have hP0 := hP.1
  have hu0 := hu.1
  have huU := hu.2
  have hw0 := hw.1
  have hwP := hw.2
  have hwsq : w ^ 2 ≤ P ^ 2 := pow_le_pow_left₀ hw.1 hw.2 2
  have H0 : |v0| * (50000 * (u + w ^ 2) / μ ^ 2) ≤ 50000 * K ^ 2 * M * (U + P ^ 2) := by
    calc
      _ = 50000 * |v0| * (u + w ^ 2) * (1 / μ) ^ 2 := by ring
      _ ≤ 50000 * (M / r ^ 2) * (U + P ^ 2) * (K * r) ^ 2 := by gcongr
      _ = _ := by field_simp
  have H1 : |v1| * (50000 / μ) ≤ 50000 * K * A * U := by
    calc
      _ = 50000 * |v1| * (1 / μ) := by ring
      _ ≤ 50000 * |v1| * (K * r) := by gcongr
      _ = 50000 * K * (r * |v1|) := by ring
      _ ≤ 50000 * K * (A * U) := by gcongr
      _ = _ := by ring
  have H2 : |v2| * (50000 * (u + w) / μ) ≤ 50000 * K * B * (U + P ^ 2) := by
    calc
      _ = 50000 * (u + w) * |v2| * (1 / μ) := by ring
      _ ≤ 50000 * (U + P) * |v2| * (K * r) := by gcongr
      _ = 50000 * K * (U + P) * (r * |v2|) := by ring
      _ ≤ 50000 * K * (U + P) * (B * P) := by gcongr
      _ = 50000 * K * B * (P * U + P ^ 2) := by ring
      _ ≤ 50000 * K * B * (U + P ^ 2) := by gcongr; exact mul_le_of_le_one_left hU hP.2
  have H1' : 50000 * K * A * U ≤ 50000 * K * A * (U + P ^ 2) :=
    mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (sq_nonneg P)) (by positivity)
  exact (add_le_add (add_le_add H0 (H1.trans H1')) H2).trans_eq (by ring)
