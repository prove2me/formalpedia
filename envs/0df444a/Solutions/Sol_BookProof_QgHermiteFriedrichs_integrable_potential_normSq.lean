-- Prove2me | solution 1 for BookProof.QgHermiteFriedrichs.integrable_potential_normSq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T08:00:29.67276+00:00
-- url     : https://prove2.me/submissions/7b7f9129-608b-49a5-913b-9d9b397ffe01

-- Generated from ChapterQgHermiteFriedrichs.lean — solution of BookProof.QgHermiteFriedrichs.integrable_potential_normSq
import Mathlib
import Definitions.Def_ChapterQgHermiteFriedrichs
import Definitions.Def_ChapterBandEnclosure
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterQgHermiteCore
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterFarisLavine
open BookProof.QgHermiteFriedrichs








open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.Starobinsky
open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.FriedrichsExtension

noncomputable section

variable {d : ℕ}































variable (W : Vd d → ℝ)

set_option maxHeartbeats 1000000 in
theorem solution (hWc : Continuous W) (hWb : ExpBounded W)
    (p : MvPolynomial (Fin d) ℂ) :
    Integrable (fun x : Vd d => W x * ‖pgFun p x‖ ^ 2) (volume : Measure (Vd d)) := by

  have hu : MemLp (fun x : Vd d => ‖pgFun p x‖) 2 (volume : Measure (Vd d)) :=
    (memLp_pgFun p).norm
  have hv : MemLp (fun x : Vd d => W x * ‖pgFun p x‖) 2 (volume : Measure (Vd d)) := by
    refine (memLp_mul_pgFun_of_expBounded hWc hWb p).of_le
      ((hWc.mul ((continuous_pgFun p).norm)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg (pgFun p x))]
  have hmul := hv.integrable_mul hu
  refine hmul.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [Pi.mul_apply]
  ring
