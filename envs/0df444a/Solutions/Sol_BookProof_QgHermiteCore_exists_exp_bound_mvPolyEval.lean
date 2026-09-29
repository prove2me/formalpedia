-- Prove2me | solution 1 for BookProof.QgHermiteCore.exists_exp_bound_mvPolyEval
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-12T08:04:52.12283+00:00
-- url     : https://prove2.me/submissions/d15c8dac-c3d2-410b-9828-f7a9a3b02276

-- Generated from ChapterQgHermiteCore.lean — solution of BookProof.QgHermiteCore.exists_exp_bound_mvPolyEval
import Mathlib
import Definitions.Def_ChapterQgHermiteCore
open BookProof.QgHermiteCore














open MeasureTheory Polynomial Filter Topology
open BookProof.HermiteCore BookProof.Starobinsky







variable {E : Type*} [NormedAddCommGroup E]





































open BookProof.HermiteProductCore

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (p : MvPolynomial (Fin d) ℂ) :
    ∃ C c : ℝ, 0 ≤ C ∧ 0 ≤ c ∧ ∀ x : Vd d,
      ‖MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) p‖ ≤ C * Real.exp (c * ‖x‖) := by

  induction p using MvPolynomial.induction_on with
  | C a =>
      refine ⟨‖a‖, 0, norm_nonneg a, le_rfl, fun x => ?_⟩
      simp
  | add p q hp hq =>
      obtain ⟨C1, c1, hC1, hc1, h1⟩ := hp
      obtain ⟨C2, c2, hC2, _, h2⟩ := hq
      refine ⟨C1 + C2, max c1 c2, by linarith, le_trans hc1 (le_max_left _ _), fun x => ?_⟩
      have e1 : C1 * Real.exp (c1 * ‖x‖) ≤ C1 * Real.exp (max c1 c2 * ‖x‖) := by
        gcongr
        exact le_max_left _ _
      have e2 : C2 * Real.exp (c2 * ‖x‖) ≤ C2 * Real.exp (max c1 c2 * ‖x‖) := by
        gcongr
        exact le_max_right _ _
      calc ‖MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (p + q)‖
          ≤ ‖MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) p‖
            + ‖MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) q‖ := by
            rw [map_add]
            exact norm_add_le _ _
        _ ≤ C1 * Real.exp (c1 * ‖x‖) + C2 * Real.exp (c2 * ‖x‖) := add_le_add (h1 x) (h2 x)
        _ ≤ (C1 + C2) * Real.exp (max c1 c2 * ‖x‖) := by linarith
  | mul_X p i hp =>
      obtain ⟨C, c, hC, hc, h⟩ := hp
      refine ⟨C, c + 1, hC, by linarith, fun x => ?_⟩
      have hxi : ‖(((x i : ℝ)) : ℂ)‖ ≤ ‖x‖ := by
        rw [Complex.norm_real]
        exact PiLp.norm_apply_le x i
      have hnorm : ‖x‖ ≤ Real.exp ‖x‖ := by
        have := Real.add_one_le_exp ‖x‖
        linarith
      calc ‖MvPolynomial.eval (fun j => ((x j : ℝ) : ℂ)) (p * MvPolynomial.X i)‖
          = ‖MvPolynomial.eval (fun j => ((x j : ℝ) : ℂ)) p‖ * ‖(((x i : ℝ)) : ℂ)‖ := by
            rw [map_mul, MvPolynomial.eval_X, norm_mul]
        _ ≤ (C * Real.exp (c * ‖x‖)) * Real.exp ‖x‖ :=
            mul_le_mul (h x) (hxi.trans hnorm) (norm_nonneg _) (by positivity)
        _ = C * Real.exp ((c + 1) * ‖x‖) := by
            rw [mul_assoc, ← Real.exp_add]
            congr 1
            ring
