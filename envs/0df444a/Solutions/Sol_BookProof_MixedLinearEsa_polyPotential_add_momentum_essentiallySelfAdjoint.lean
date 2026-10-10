-- Prove2me | solution 1 for BookProof.MixedLinearEsa.polyPotential_add_momentum_essentiallySelfAdjoint
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T22:04:57.748604+00:00
-- url     : https://prove2.me/submissions/663b7457-7af7-48e4-83f2-d2a1de0cb15b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterMixedLinearEsa.lean — solution of BookProof.MixedLinearEsa.polyPotential_add_momentum_essentiallySelfAdjoint
import Mathlib
import Definitions.Def_ChapterMixedLinearEsa
import Theorems.Thm_BookProof_MixedLinearEsa_potMomOp_essentiallySelfAdjoint
import Theorems.Thm_BookProof_MixedLinearEsa_hasTemperateGrowth_polyPotential
import Theorems.Thm_BookProof_MixedLinearEsa_contDiff_polyPhase
import Theorems.Thm_BookProof_MixedLinearEsa_hasDerivAt_polyPhase_line
import Definitions.Def_ChapterFourierMultiplierEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterStrichartzWave
open BookProof.MixedLinearEsa




open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace LineDeriv
open BookProof.StrichartzWave BookProof.FourierMultiplierEsa BookProof.FarisLavine

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

set_option maxHeartbeats 1000000 in
theorem solution (c : ℕ → ℝ) (n : ℕ) {m : V}
    (hm : m ≠ 0) :
    EssentiallySelfAdjointOn (schwartzDomain V) (opL2 (potMomOp (polyPotential c n m) m)) :=
  potMomOp_essentiallySelfAdjoint (hasTemperateGrowth_polyPotential c n m)
      (contDiff_polyPhase c n m) (hasDerivAt_polyPhase_line c n hm)
