-- Prove2me | solution 1 for BookProof.QgHermiteCore.memLp_mul_pgFun_of_expBounded
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-12T08:07:43.407403+00:00
-- url     : https://prove2.me/submissions/f2504916-d279-47d0-98e5-433e297d1be1

-- Generated from ChapterQgHermiteCore.lean — solution of BookProof.QgHermiteCore.memLp_mul_pgFun_of_expBounded
import Mathlib
import Definitions.Def_ChapterQgHermiteCore
import Theorems.Thm_BookProof_QgHermiteCore_ExpBounded_nonneg_const
import Theorems.Thm_BookProof_QgHermiteCore_exists_exp_bound_mvPolyEval
open BookProof.QgHermiteCore














open MeasureTheory Polynomial Filter Topology
open BookProof.HermiteCore BookProof.Starobinsky







variable {E : Type*} [NormedAddCommGroup E]





































open BookProof.HermiteProductCore

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {W : Vd d → ℝ} (hW : Continuous W) (hWb : ExpBounded W)
    (p : MvPolynomial (Fin d) ℂ) :
    MemLp (fun x : Vd d => ((W x : ℝ) : ℂ) * pgFun p x) 2 (volume : Measure (Vd d)) := by

  obtain ⟨CW, cW, hcW, hW1⟩ := hWb
  have hCW : 0 ≤ CW := ExpBounded.nonneg_const hW1
  obtain ⟨Cp, cp, hCp, hcp, hp1⟩ := exists_exp_bound_mvPolyEval p
  have hmaj : MemLp (fun x : Vd d => ((CW * Cp : ℝ) : ℂ)
      * ((Real.exp ((cW + cp) * ‖x‖) * gaussD x : ℝ) : ℂ)) 2 (volume : Measure (Vd d)) :=
    (memLp_two_exp_norm_mul_gaussD (cW + cp)).const_mul _
  refine hmaj.of_le ?_ (Filter.Eventually.of_forall fun x => ?_)
  · exact ((Complex.continuous_ofReal.comp hW).mul (continuous_pgFun p)).aestronglyMeasurable
  · have hg : 0 < gaussD x := gaussD_pos x
    have hexp : Real.exp (cW * ‖x‖) * Real.exp (cp * ‖x‖) = Real.exp ((cW + cp) * ‖x‖) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hlhs : ‖((W x : ℝ) : ℂ) * pgFun p x‖
        = |W x| * (‖MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) p‖ * gaussD x) := by
      rw [pgFun, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_pos hg]
    have hrhs : ‖((CW * Cp : ℝ) : ℂ) * ((Real.exp ((cW + cp) * ‖x‖) * gaussD x : ℝ) : ℂ)‖
        = CW * Cp * (Real.exp ((cW + cp) * ‖x‖) * gaussD x) := by
      rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ CW * Cp),
        abs_of_nonneg (by positivity : (0:ℝ) ≤ Real.exp ((cW + cp) * ‖x‖) * gaussD x)]
    rw [hlhs, hrhs]
    calc |W x| * (‖MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) p‖ * gaussD x)
        ≤ (CW * Real.exp (cW * ‖x‖)) * ((Cp * Real.exp (cp * ‖x‖)) * gaussD x) := by
          have h2 : ‖MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) p‖ * gaussD x
              ≤ (Cp * Real.exp (cp * ‖x‖)) * gaussD x :=
            mul_le_mul_of_nonneg_right (hp1 x) hg.le
          exact mul_le_mul (hW1 x) h2 (by positivity) (by positivity)
      _ = CW * Cp * ((Real.exp (cW * ‖x‖) * Real.exp (cp * ‖x‖)) * gaussD x) := by ring
      _ = CW * Cp * (Real.exp ((cW + cp) * ‖x‖) * gaussD x) := by rw [hexp]
