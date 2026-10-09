-- Prove2me | solution 1 for BookProof.FourierMultiplierEsa.mixedOp_essentiallySelfAdjoint
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:16:34.78513+00:00
-- url     : https://prove2.me/submissions/12589b78-d8b4-479c-b36e-b2d3e7c0a173
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterFourierMultiplierEsa.lean — solution of BookProof.FourierMultiplierEsa.mixedOp_essentiallySelfAdjoint
import Mathlib
import Definitions.Def_ChapterFourierMultiplierEsa
import Theorems.Thm_BookProof_FourierMultiplierEsa_essentiallySelfAdjointOn_of_real_symbol
import Theorems.Thm_BookProof_FourierMultiplierEsa_contDiff_mixedSymbolFn
import Theorems.Thm_BookProof_FourierMultiplierEsa_fourier_mixedOp_apply
open BookProof.FourierMultiplierEsa




open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace LineDeriv
open BookProof.StrichartzWave

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {ι : Type*} [Fintype ι]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {ι : Type*} [Fintype ι]

set_option maxHeartbeats 1000000 in
theorem solution (a c : ι → ℝ) (w : ι → V) (κ : ℝ) :
    BookProof.FarisLavine.EssentiallySelfAdjointOn (schwartzDomain V)
      (opL2 (mixedOp a c w κ)) :=
  essentiallySelfAdjointOn_of_real_symbol _ _ (fourier_mixedOp_apply a c w κ)
      (contDiff_mixedSymbolFn a c w κ)
