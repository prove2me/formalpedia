-- Prove2me | solution 1 for BianchiIX.reciprocal_gauss_estimates
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T07:06:20.929902+00:00
-- url     : https://prove2.me/submissions/fe08bb5e-d466-4ef0-b235-ba90fd51a66f

import Definitions.Def_BianchiIX_Statistics_GaussInverse
import Theorems.Thm_BianchiIX_abs_log_le_twice_error
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.List.Induction

noncomputable section
open BianchiIX

section
open BianchiIX
noncomputable section
open Filter
open scoped Topology

private theorem BianchiIX.hasDerivAt_gaussInv {a x : ℝ} (ha : 1 ≤ a) (hx : 0 ≤ x) :
    HasDerivAt (gaussInv a) (-1 / (a + x) ^ 2) x := by
  have hden : a + x ≠ 0 := ne_of_gt (by linarith)
  unfold gaussInv
  simpa only [one_div, id_eq] using ((hasDerivAt_id x).const_add a).fun_inv hden

end
end

/-- Reciprocal coordinates retain the digit-square value gain and add only four times the phase error. -/
theorem solution {k : ℝ → ℝ} {n y d E D : ℝ}
    (hn : 1 ≤ n) (hy : 0 ≤ y) (hk : n ≤ k y)
    (Hk : HasDerivAt k d y) (hd : 0 < d)
    (hvalue : |k y - (n + y)| ≤ E) (hsmall : E ≤ 1 / 4)
    (hlog : |Real.log d| ≤ D) :
    let h := fun z => 1 / k z
    HasDerivAt h (-d / (k y) ^ 2) y ∧ deriv h y < 0 ∧
      |h y - gaussInv n y| ≤ E / n ^ 2 ∧
      |Real.log (|deriv h y| / |deriv (gaussInv n) y|)| ≤ D + 4 * E := by
  intro h
  have hn0 : 0 < n := by linarith
  have hk1 : 1 ≤ k y := hn.trans hk
  have hk0 : 0 < k y := by linarith
  have hp0 : 0 < n + y := by linarith
  have hE : 0 ≤ E := (abs_nonneg _).trans hvalue
  have Hh : HasDerivAt h (-d / (k y) ^ 2) y := by
    simpa only [h, one_div] using Hk.fun_inv hk0.ne'
  have hden : n ^ 2 ≤ k y * (n + y) := by
    calc
      _ = n * n := pow_two n
      _ ≤ k y * (n + y) := mul_le_mul hk (by linarith) hn0.le hk0.le
  have hratio : |(n + y) / k y - 1| ≤ E := by
    rw [show (n + y) / k y - 1 = ((n + y) - k y) / k y by field_simp,
      abs_div, abs_of_pos hk0, abs_sub_comm]
    exact (div_le_div_of_nonneg_right hvalue hk0.le).trans (div_le_self hE hk1)
  have hratio0 : 0 < (n + y) / k y := div_pos hp0 hk0
  have hlratio := abs_log_le_twice_error hsmall hratio
  have hneg : -d / (k y) ^ 2 < 0 := div_neg_of_neg_of_pos (neg_neg_of_pos hd) (sq_pos_of_pos hk0)
  refine ⟨Hh, Hh.deriv ▸ hneg, ?_, ?_⟩
  · change |1 / k y - 1 / (n + y)| ≤ _
    rw [show 1 / k y - 1 / (n + y) = ((n + y) - k y) / (k y * (n + y)) by
      field_simp, abs_div, abs_of_pos (mul_pos hk0 hp0), abs_sub_comm]
    exact (div_le_div_of_nonneg_right hvalue (mul_pos hk0 hp0).le).trans
      (div_le_div_of_nonneg_left hE (sq_pos_of_pos hn0) hden)
  · rw [Hh.deriv, (hasDerivAt_gaussInv hn hy).deriv, abs_of_neg hneg,
      abs_of_neg (div_neg_of_neg_of_pos (by norm_num : (-1 : ℝ) < 0) (sq_pos_of_pos hp0))]
    have halg : -(-d / (k y) ^ 2) / -(-1 / (n + y) ^ 2) =
        d * ((n + y) / k y) ^ 2 := by field_simp
    rw [halg, Real.log_mul hd.ne' (pow_ne_zero _ hratio0.ne'), Real.log_pow]
    calc
      _ ≤ |Real.log d| + |(2 : ℝ) * Real.log ((n + y) / k y)| := abs_add_le _ _
      _ = |Real.log d| + 2 * |Real.log ((n + y) / k y)| := by
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      _ ≤ D + 4 * E := by linarith
