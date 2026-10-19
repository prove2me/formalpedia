-- Prove2me | solution 1 for BookProof.MixedLinearEsa.mixedLinearOp_apply
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:39:14.405264+00:00
-- url     : https://prove2.me/submissions/e15f16b5-ec7d-4a0b-a4b6-4f4f65387032

import Definitions.Def_ChapterStrichartzWave
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterMixedLinearEsa
import Definitions.Def_ChapterFourierMultiplierEsa
-- Generated from ChapterMixedLinearEsa.lean — theorem BookProof.MixedLinearEsa.mixedLinearOp_apply
open BookProof.FourierMultiplierEsa
open BookProof.MixedLinearEsa



open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace LineDeriv
open BookProof.StrichartzWave BookProof.FourierMultiplierEsa BookProof.FarisLavine

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]


theorem solution (b m : V) (f : 𝓢(V, ℂ)) (x : V) :
    (mixedLinearOp b m f) x
      = ((inner ℝ x b : ℝ) : ℂ) * f x + (-Complex.I) * (fderiv ℝ f x m) := by
  have hg : Function.HasTemperateGrowth (fun x : V => ((inner ℝ x b : ℝ) : ℂ)) :=
    (Complex.ofRealCLM.comp ((innerSL ℝ).flip b)).hasTemperateGrowth
  simp only [mixedLinearOp, posOp, momentumOp, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, lineDerivOpCLM_apply, SchwartzMap.add_apply,
    SchwartzMap.smul_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv, smul_eq_mul,
    SchwartzMap.smulLeftCLM_apply_apply hg]

