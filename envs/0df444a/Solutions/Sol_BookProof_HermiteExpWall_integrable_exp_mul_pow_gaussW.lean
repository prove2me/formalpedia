-- Prove2me | solution 1 for BookProof.HermiteExpWall.integrable_exp_mul_pow_gaussW
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T15:02:43.311978+00:00
-- url     : https://prove2.me/submissions/a72eaa6e-178d-49ea-a8e4-2409437dd78d

-- Generated from ChapterHermiteExpWall.lean — solution of BookProof.HermiteExpWall.integrable_exp_mul_pow_gaussW
import Mathlib
import Definitions.Def_ChapterHermiteExpWall
import Theorems.Thm_BookProof_QgHermiteCore_exp_abs_le_const_mul_exp_sq
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterQgHermiteCore
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteFunctions
open BookProof.HermiteExpWall




open MeasureTheory Polynomial
open BookProof.HermiteCore BookProof.Starobinsky BookProof.QgHermiteCore
open BookProof.HermiteProductCore
open BookProof.HermiteCore

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution (c : ℝ) (k : ℕ) :
    Integrable (fun x : ℝ => Real.exp (c * x) * (x ^ k * gaussW x)) := by

  have hdom : Integrable
      (fun x : ℝ => Real.exp (2 * c ^ 2) * ‖x ^ k * Real.exp (-(3 / 8 : ℝ) * x ^ 2)‖) :=
    ((integrable_pow_mul_exp_neg k (by norm_num : (0:ℝ) < 3 / 8)).norm).const_mul _
  refine hdom.mono' (Continuous.aestronglyMeasurable (by unfold gaussW; fun_prop)) ?_
  filter_upwards with x
  have h1 : Real.exp (c * x) ≤ Real.exp (|c| * |x|) := by
    refine Real.exp_le_exp.mpr ?_
    calc c * x ≤ |c * x| := le_abs_self _
      _ = |c| * |x| := abs_mul c x
  have h2 : Real.exp (|c| * |x|) ≤ Real.exp (2 * |c| ^ 2) * Real.exp (x ^ 2 / 8) :=
    exp_abs_le_const_mul_exp_sq |c| x
  have hc : (2 : ℝ) * |c| ^ 2 = 2 * c ^ 2 := by rw [sq_abs]
  have hnorm : ‖Real.exp (c * x) * (x ^ k * gaussW x)‖
      = Real.exp (c * x) * (|x| ^ k * Real.exp (-x ^ 2 / 2)) := by
    rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, abs_pow,
      abs_of_pos (Real.exp_pos _), gaussW, abs_of_pos (Real.exp_pos _)]
  have hnorm2 : ‖x ^ k * Real.exp (-(3 / 8 : ℝ) * x ^ 2)‖
      = |x| ^ k * Real.exp (-(3 / 8) * x ^ 2) := by
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_pow, abs_of_pos (Real.exp_pos _)]
  rw [hnorm, hnorm2]
  calc Real.exp (c * x) * (|x| ^ k * Real.exp (-x ^ 2 / 2))
      ≤ (Real.exp (2 * c ^ 2) * Real.exp (x ^ 2 / 8)) * (|x| ^ k * Real.exp (-x ^ 2 / 2)) := by
        gcongr
        calc Real.exp (c * x) ≤ Real.exp (|c| * |x|) := h1
          _ ≤ Real.exp (2 * |c| ^ 2) * Real.exp (x ^ 2 / 8) := h2
          _ = Real.exp (2 * c ^ 2) * Real.exp (x ^ 2 / 8) := by rw [hc]
    _ = Real.exp (2 * c ^ 2) * (|x| ^ k * Real.exp (-(3 / 8) * x ^ 2)) := by
        rw [show (-(3 / 8 : ℝ) * x ^ 2) = x ^ 2 / 8 + (-x ^ 2 / 2) by ring, Real.exp_add]
        ring
