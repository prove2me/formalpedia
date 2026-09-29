-- Prove2me | solution 1 for BookProof.StrichartzWave.wave_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-18T09:38:08.302944+00:00
-- url     : https://prove2.me/submissions/30cea4f4-caf9-4f92-ad6d-94fec7ec2e3c

-- Generated from ChapterStrichartzWave.lean — solution of BookProof.StrichartzWave.wave_symmetric
import Mathlib
import Definitions.Def_ChapterStrichartzWave
import Theorems.Thm_BookProof_StrichartzWave_constCoeffOp_symmetric
open BookProof.StrichartzWave











open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace LineDeriv

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {ι : Type*} [Fintype ι]

set_option maxHeartbeats 1000000 in
theorem solution (n : ℕ) (κ : ℝ) :
    BookProof.FarisLavine.SymmetricOn (schwartzDomain (SpaceTime n)) (opL2 (waveOp n κ)) := constCoeffOp_symmetric _ _ _
