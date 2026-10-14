-- Prove2me | solution 1 for BookProof.StrichartzWave.multiplierOp_symmetric
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T20:45:09.662935+00:00
-- url     : https://prove2.me/submissions/2dce0843-0477-4621-9d43-e7e982a18185
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterWaveUnboundedPotential.lean — solution of BookProof.StrichartzWave.multiplierOp_symmetric
import Mathlib
import Definitions.Def_ChapterWaveUnboundedPotential
import Theorems.Thm_BookProof_StrichartzWave_fourier_multiplierOp_apply
import Theorems.Thm_BookProof_StrichartzWave_inner_toLp_eq_integral_fourier
import Theorems.Thm_BookProof_StrichartzWave_opL2_apply
import Theorems.Thm_BookProof_StrichartzWave_schwartzEquiv_coe
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterStrichartzWave
open BookProof.StrichartzWave




open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace ENNReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

set_option maxHeartbeats 1000000 in
theorem solution (m : V → ℝ) (hm : Function.HasTemperateGrowth m) :
    BookProof.FarisLavine.SymmetricOn (schwartzDomain V) (opL2 (multiplierOp m)) := by

  intro x y
  obtain ⟨f, rfl⟩ := (schwartzEquiv V).surjective x
  obtain ⟨g, rfl⟩ := (schwartzEquiv V).surjective y
  rw [opL2_apply, opL2_apply, schwartzEquiv_coe, schwartzEquiv_coe,
    inner_toLp_eq_integral_fourier, inner_toLp_eq_integral_fourier]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [fourier_multiplierOp_apply hm, map_mul, Complex.conj_ofReal]
  ring
