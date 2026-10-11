-- Prove2me | solution 1 for BookProof.ScalaronHermiteEsa.gaussExpDecay_of_memLp_mul
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:18:58.080488+00:00
-- url     : https://prove2.me/submissions/35bb434a-9c28-458d-854c-a3b00050b4ae

-- Generated from ChapterScalaronHermiteEsa.lean — solution of BookProof.ScalaronHermiteEsa.gaussExpDecay_of_memLp_mul
import Mathlib
import Definitions.Def_ChapterScalaronHermiteEsa
import Theorems.Thm_BookProof_ScalaronHermiteEsa_continuous_expGauss
import Theorems.Thm_BookProof_ScalaronHermiteEsa_norm_expGauss
import Definitions.Def_ChapterQgHermiteCore
import Definitions.Def_ChapterQgHermiteFriedrichs
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterHermiteFunctions
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
theorem solution {u w : Vd d → ℂ} {C c : ℝ}
    (hu : AEStronglyMeasurable u (volume : Measure (Vd d)))
    (hw : MemLp w 2 (volume : Measure (Vd d)))
    (hbd : ∀ x, ‖u x‖ ≤ C * Real.exp (c * ‖x‖) * ‖w x‖) :
    GaussExpDecay u := by

  intro s
  have hmaj : Integrable
      (fun x : Vd d => ((Real.exp ((s + c) * ‖x‖) * gaussD x : ℝ) : ℂ) * w x) :=
    integrable_mul_of_memLp_two (memLp_two_exp_norm_mul_gaussD (s + c)) hw
  refine Integrable.mono' (hmaj.norm.const_mul C)
    ((continuous_expGauss s).aestronglyMeasurable.mul hu)
    (Filter.Eventually.of_forall fun x => ?_)
  have hexp : Real.exp ((s + c) * ‖x‖) = Real.exp (s * ‖x‖) * Real.exp (c * ‖x‖) := by
    rw [← Real.exp_add]; ring_nf
  rw [norm_mul, norm_expGauss, norm_mul, norm_expGauss, hexp]
  have h1 : Real.exp (s * ‖x‖) * gaussD x * ‖u x‖
      ≤ Real.exp (s * ‖x‖) * gaussD x * (C * Real.exp (c * ‖x‖) * ‖w x‖) :=
    mul_le_mul_of_nonneg_left (hbd x) (mul_pos (Real.exp_pos _) (gaussD_pos x)).le
  calc Real.exp (s * ‖x‖) * gaussD x * ‖u x‖
      ≤ Real.exp (s * ‖x‖) * gaussD x * (C * Real.exp (c * ‖x‖) * ‖w x‖) := h1
    _ = C * (Real.exp (s * ‖x‖) * Real.exp (c * ‖x‖) * gaussD x * ‖w x‖) := by ring
