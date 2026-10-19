-- Prove2me | solution 1 for BookProof.MixedLinearEsa.potMomOp_apply
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:39:33.485855+00:00
-- url     : https://prove2.me/submissions/bffd8e10-b870-4444-bfd8-6ef15c02d666

import Definitions.Def_ChapterStrichartzWave
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterMixedLinearEsa
import Definitions.Def_ChapterFourierMultiplierEsa
import Definitions.Def_ChapterWaveUnboundedPotential
-- Generated from ChapterMixedLinearEsa.lean — theorem BookProof.MixedLinearEsa.potMomOp_apply
open BookProof.FourierMultiplierEsa
open BookProof.MixedLinearEsa



open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace LineDeriv
open BookProof.StrichartzWave BookProof.FourierMultiplierEsa BookProof.FarisLavine

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]




omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem solution {W : V → ℝ} (hW : Function.HasTemperateGrowth W) (m : V) (f : 𝓢(V, ℂ))
    (x : V) :
    (potMomOp W m f) x = ((W x : ℝ) : ℂ) * f x + (-Complex.I) * (fderiv ℝ f x m) := by
  have hg : Function.HasTemperateGrowth (fun x : V => ((W x : ℝ) : ℂ)) :=
    Function.HasTemperateGrowth.comp Complex.ofRealCLM.hasTemperateGrowth hW
  simp only [potMomOp, potentialOp, momentumOp, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, lineDerivOpCLM_apply, SchwartzMap.add_apply,
    SchwartzMap.smul_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv, smul_eq_mul,
    SchwartzMap.smulLeftCLM_apply_apply hg]

