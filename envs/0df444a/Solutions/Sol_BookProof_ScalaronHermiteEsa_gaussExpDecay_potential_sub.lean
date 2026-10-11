-- Prove2me | solution 1 for BookProof.ScalaronHermiteEsa.gaussExpDecay_potential_sub
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:21:01.755998+00:00
-- url     : https://prove2.me/submissions/3042f2ab-3f2e-40c0-acb2-498122523260

-- Generated from ChapterScalaronHermiteEsa.lean — solution of BookProof.ScalaronHermiteEsa.gaussExpDecay_potential_sub
import Mathlib
import Definitions.Def_ChapterScalaronHermiteEsa
import Theorems.Thm_BookProof_ScalaronHermiteEsa_gaussExpDecay_of_memLp_mul
import Definitions.Def_ChapterQgHermiteFriedrichs
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterQgHermiteCore
open BookProof.ScalaronHermiteEsa




open MeasureTheory Complex MvPolynomial FourierTransform
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgHermiteOscillator BookProof.FarisLavine BookProof.Starobinsky
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {W : Vd d → ℝ} (hWc : Continuous W) (hWb : ExpBounded W)
    (z : ℂ) (w : L2d d) :
    GaussExpDecay (fun x : Vd d => (((W x : ℝ) : ℂ) - z) * (w : Vd d → ℂ) x) := by

  obtain ⟨CW, cW, hcW, hWbd⟩ := hWb
  have hWm : AEStronglyMeasurable (fun x : Vd d => ((W x : ℝ) : ℂ))
      (volume : Measure (Vd d)) :=
    (Complex.continuous_ofReal.comp hWc).aestronglyMeasurable
  refine gaussExpDecay_of_memLp_mul (C := CW + ‖z‖) (c := cW)
    ((hWm.sub aestronglyMeasurable_const).mul (Lp.memLp w).1) (Lp.memLp w) fun x => ?_
  have h1 : ‖((W x : ℝ) : ℂ) - z‖ ≤ CW * Real.exp (cW * ‖x‖) + ‖z‖ := by
    refine (norm_sub_le _ _).trans ?_
    have hWx : ‖((W x : ℝ) : ℂ)‖ ≤ CW * Real.exp (cW * ‖x‖) := by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact hWbd x
    linarith
  have h2 : CW * Real.exp (cW * ‖x‖) + ‖z‖ ≤ (CW + ‖z‖) * Real.exp (cW * ‖x‖) := by
    have hge : (1 : ℝ) ≤ Real.exp (cW * ‖x‖) := Real.one_le_exp (by positivity)
    nlinarith [norm_nonneg z]
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (h1.trans h2) (norm_nonneg _)
