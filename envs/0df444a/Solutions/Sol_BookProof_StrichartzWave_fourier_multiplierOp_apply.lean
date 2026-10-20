-- Prove2me | solution 1 for BookProof.StrichartzWave.fourier_multiplierOp_apply
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T15:30:52.393055+00:00
-- url     : https://prove2.me/submissions/bb3d5a50-76ab-46e4-989a-37328ee65cbc

-- Generated from ChapterWaveUnboundedPotential.lean — theorem BookProof.StrichartzWave.fourier_multiplierOp_apply
import Mathlib
import Definitions.Def_ChapterWaveUnboundedPotential
import Definitions.Def_ChapterStrichartzWave
open BookProof.StrichartzWave



open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace ENNReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
open BookProof.StrichartzWave in
theorem solution {m : V → ℝ} (hm : Function.HasTemperateGrowth m)
    (f : 𝓢(V, ℂ)) (x : V) :
    (𝓕 (multiplierOp m f) : 𝓢(V, ℂ)) x = ((m x : ℝ) : ℂ) * (𝓕 f : 𝓢(V, ℂ)) x := by 
  have hm' : Function.HasTemperateGrowth (fun x : V => ((m x : ℝ) : ℂ)) :=
    (Complex.ofRealCLM.hasTemperateGrowth).comp hm
  simp only [multiplierOp, potentialOp, ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearEquiv.coe_coe]
  rw [FourierTransform.fourierCLE_apply, FourierTransform.fourierCLE_symm_apply, FourierTransform.fourier_fourierInv_eq,
    SchwartzMap.smulLeftCLM_apply_apply hm', smul_eq_mul]
