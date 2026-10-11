-- Prove2me | solution 1 for BookProof.ScalaronHermiteEsa.GaussExpDecay.aestronglyMeasurable
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:18:56.978289+00:00
-- url     : https://prove2.me/submissions/4cc21acd-76f0-4161-8166-db526890ec24

-- Generated from ChapterScalaronHermiteEsa.lean — solution of BookProof.ScalaronHermiteEsa.GaussExpDecay.aestronglyMeasurable
import Mathlib
import Definitions.Def_ChapterScalaronHermiteEsa
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
theorem solution {u : Vd d → ℂ} (hu : GaussExpDecay u) :
    AEStronglyMeasurable u (volume : Measure (Vd d)) := by

  have h0 := (hu 0).aestronglyMeasurable
  simp only [zero_mul, Real.exp_zero, one_mul] at h0
  have hinv : Continuous fun x : Vd d => (((gaussD x)⁻¹ : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp
      (continuous_gaussD.inv₀ fun x => ne_of_gt (gaussD_pos x))
  refine (hinv.aestronglyMeasurable.mul h0).congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [Pi.mul_apply]
  rw [← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ (ne_of_gt (gaussD_pos x)),
    Complex.ofReal_one, one_mul]
