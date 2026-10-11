-- Prove2me | solution 1 for BookProof.ScalaronHermiteEsa.gaussExpDecay_mul_lp
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:19:31.842099+00:00
-- url     : https://prove2.me/submissions/19e57d9d-1178-4e10-b77a-8309e07fa4c2

-- Generated from ChapterScalaronHermiteEsa.lean — solution of BookProof.ScalaronHermiteEsa.gaussExpDecay_mul_lp
import Mathlib
import Definitions.Def_ChapterScalaronHermiteEsa
import Theorems.Thm_BookProof_ScalaronHermiteEsa_gaussExpDecay_of_memLp_mul
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
theorem solution {g : Vd d → ℂ} {C c : ℝ}
    (hg : AEStronglyMeasurable g (volume : Measure (Vd d)))
    (hbd : ∀ x, ‖g x‖ ≤ C * Real.exp (c * ‖x‖)) (w : L2d d) :
    GaussExpDecay (fun x : Vd d => g x * (w : Vd d → ℂ) x) := by

  refine gaussExpDecay_of_memLp_mul (C := C) (c := c) (hg.mul (Lp.memLp w).1) (Lp.memLp w)
    fun x => ?_
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hbd x) (norm_nonneg _)
