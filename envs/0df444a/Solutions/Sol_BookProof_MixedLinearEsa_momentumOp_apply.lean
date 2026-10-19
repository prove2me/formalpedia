-- Prove2me | solution 1 for BookProof.MixedLinearEsa.momentumOp_apply
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:39:01.139664+00:00
-- url     : https://prove2.me/submissions/dbc0f84b-80dc-433b-8b5b-38c68953c67a

import Definitions.Def_ChapterStrichartzWave
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterMixedLinearEsa
import Definitions.Def_ChapterFourierMultiplierEsa
-- Generated from ChapterMixedLinearEsa.lean — theorem BookProof.MixedLinearEsa.momentumOp_apply
open BookProof.FourierMultiplierEsa
open BookProof.MixedLinearEsa



open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace LineDeriv
open BookProof.StrichartzWave BookProof.FourierMultiplierEsa BookProof.FarisLavine

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]


theorem solution (m : V) (f : 𝓢(V, ℂ)) (x : V) :
    (momentumOp m f) x = (-Complex.I) * (fderiv ℝ f x m) := by
  simp only [momentumOp, ContinuousLinearMap.smul_apply, lineDerivOpCLM_apply,
    SchwartzMap.smul_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv, smul_eq_mul]

