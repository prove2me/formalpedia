-- Prove2me | solution 1 for BianchiIX.curvature_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T05:36:52.35325+00:00
-- url     : https://prove2.me/submissions/d7cce9ac-0af9-464b-ae28-5a10bdfd00fc

import Definitions.Def_BianchiIX_Algebra_Flow
import Definitions.Def_BianchiIX_Algebra_Flux
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp

open BianchiIX
noncomputable section

private theorem BianchiIX.ordered_arithmetic_geometric
    {a b c r : ℝ} (hc : 0 ≤ c) (hcb : c ≤ b) (hba : b ≤ a)
    (hr : r ^ 3 = a * b * c) : 3 * r ≤ a + b + c := by
  have hid : (a + b + c) ^ 3 - 27 * (a * b * c) =
      9 * c * ((a - b) ^ 2 + (a - b) * (b - c) + (b - c) ^ 2) +
        (a + b - 2 * c) ^ 3 := by ring
  have hnonneg : 0 ≤
      9 * c * ((a - b) ^ 2 + (a - b) * (b - c) + (b - c) ^ 2) +
        (a + b - 2 * c) ^ 3 :=
    add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hc)
      (add_nonneg (add_nonneg (sq_nonneg _)
        (mul_nonneg (sub_nonneg.mpr hba) (sub_nonneg.mpr hcb))) (sq_nonneg _)))
      (pow_nonneg (by linarith) 3)
  apply (show Odd 3 by decide).pow_le_pow.mp
  nlinarith only [hid, hnonneg, hr]

private theorem BianchiIX.schur_identity {a b c r : ℝ} (hr : r ^ 3 = a * b * c) :
    (a + b + c) * (curvature a b c + 3 * r ^ 2) =
      (a - b) ^ 2 * (a + b - c) + c * (a - c) * (b - c) +
        3 * r ^ 2 * (a + b + c - 3 * r) := by
  unfold curvature
  nlinarith only [hr]

private theorem BianchiIX.ordered_curvature_lower_bound
    {a b c r : ℝ} (hc : 0 < c) (hcb : c ≤ b) (hba : b ≤ a)
    (hr : r ^ 3 = a * b * c) : -3 * r ^ 2 ≤ curvature a b c := by
  have ham := ordered_arithmetic_geometric hc.le hcb hba hr
  have h1 : 0 ≤ (a - b) ^ 2 * (a + b - c) :=
    mul_nonneg (sq_nonneg _) (by linarith)
  have h2 : 0 ≤ c * (a - c) * (b - c) :=
    mul_nonneg (mul_nonneg hc.le (by linarith)) (sub_nonneg.mpr hcb)
  have h3 : 0 ≤ 3 * r ^ 2 * (a + b + c - 3 * r) :=
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (sub_nonneg.mpr ham)
  have hprod : 0 ≤ (a + b + c) * (curvature a b c + 3 * r ^ 2) := by
    rw [schur_identity hr]
    exact add_nonneg (add_nonneg h1 h2) h3
  have hsum : 0 < a + b + c := by linarith
  have := (mul_nonneg_iff_of_pos_left hsum).mp hprod
  linarith

/-- The cube-root relation specifies r; neither ordering nor AM-GM is assumed. -/
theorem solution
    {a b c r : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hr : r ^ 3 = a * b * c) : -3 * r ^ 2 ≤ curvature a b c := by
  rcases le_total b a with hba | hab
  · rcases le_total c b with hcb | hbc
    · exact ordered_curvature_lower_bound hc hcb hba hr
    · rcases le_total c a with hca | hac
      · have h := ordered_curvature_lower_bound hb hbc hca
          (show r ^ 3 = a * c * b by nlinarith only [hr])
        convert h using 1
        unfold curvature
        ring
      · have h := ordered_curvature_lower_bound hb hba hac
          (show r ^ 3 = c * a * b by nlinarith only [hr])
        convert h using 1
        unfold curvature
        ring
  · rcases le_total c a with hca | hac
    · have h := ordered_curvature_lower_bound hc hca hab
        (show r ^ 3 = b * a * c by nlinarith only [hr])
      convert h using 1
      unfold curvature
      ring
    · rcases le_total c b with hcb | hbc
      · have h := ordered_curvature_lower_bound ha hac hcb
          (show r ^ 3 = b * c * a by nlinarith only [hr])
        convert h using 1
        unfold curvature
        ring
      · have h := ordered_curvature_lower_bound ha hab hbc
          (show r ^ 3 = c * b * a by nlinarith only [hr])
        convert h using 1
        unfold curvature
        ring
