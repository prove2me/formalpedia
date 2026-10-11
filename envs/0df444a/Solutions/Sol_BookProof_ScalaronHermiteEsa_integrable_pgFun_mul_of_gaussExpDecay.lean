-- Prove2me | solution 1 for BookProof.ScalaronHermiteEsa.integrable_pgFun_mul_of_gaussExpDecay
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:19:28.826402+00:00
-- url     : https://prove2.me/submissions/9d26a6f1-b73e-48a2-9ba6-b9f6bb080b47

-- Generated from ChapterScalaronHermiteEsa.lean — solution of BookProof.ScalaronHermiteEsa.integrable_pgFun_mul_of_gaussExpDecay
import Mathlib
import Definitions.Def_ChapterScalaronHermiteEsa
import Theorems.Thm_BookProof_ScalaronHermiteEsa_norm_expGauss
import Theorems.Thm_BookProof_ScalaronHermiteEsa_GaussExpDecay_aestronglyMeasurable
import Theorems.Thm_BookProof_QgHermiteCore_exists_exp_bound_mvPolyEval
import Definitions.Def_ChapterQgHermiteCore
import Definitions.Def_ChapterQgHermiteFriedrichs
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterHermiteProductCore
open BookProof.ScalaronHermiteEsa




open MeasureTheory Complex MvPolynomial FourierTransform
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgHermiteOscillator BookProof.FarisLavine BookProof.Starobinsky
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {u : Vd d → ℂ} (hu : GaussExpDecay u)
    (p : MvPolynomial (Fin d) ℂ) : Integrable (fun x : Vd d => pgFun p x * u x) := by

  obtain ⟨C, c, hC, hc, hb⟩ := exists_exp_bound_mvPolyEval p
  refine Integrable.mono' ((hu c).norm.const_mul C)
    ((continuous_pgFun p).aestronglyMeasurable.mul hu.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x => ?_)
  rw [norm_mul, pgFun, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (gaussD_pos x), norm_mul, norm_expGauss]
  have hnn : (0 : ℝ) ≤ gaussD x * ‖u x‖ := mul_nonneg (gaussD_pos x).le (norm_nonneg _)
  calc ‖MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) p‖ * gaussD x * ‖u x‖
      = ‖MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) p‖ * (gaussD x * ‖u x‖) := by ring
    _ ≤ C * Real.exp (c * ‖x‖) * (gaussD x * ‖u x‖) :=
        mul_le_mul_of_nonneg_right (hb x) hnn
    _ = C * (Real.exp (c * ‖x‖) * gaussD x * ‖u x‖) := by ring
