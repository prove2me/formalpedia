-- Prove2me | solution 1 for BookProof.NsFieldMomentumInverse.mem_momDomain_iff
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:44:33.588984+00:00
-- url     : https://prove2.me/submissions/72aeee13-ecf0-4427-984a-7f117fd55662

-- Generated from ChapterNsFieldMomentumInverse.lean — solution of BookProof.NsFieldMomentumInverse.mem_momDomain_iff
import Mathlib
import Definitions.Def_ChapterNsFieldMomentumInverse
import Definitions.Def_ChapterNsSpatialMomentumMultiplier
import Definitions.Def_ChapterFourierMultiplierEsa
import Definitions.Def_ChapterStrichartzWave
open BookProof.NsFieldMomentumInverse




open MeasureTheory SchwartzMap FourierTransform
open BookProof.NsSpatialMultiplier BookProof.FourierMultiplierEsa BookProof.StrichartzWave

noncomputable section

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]

set_option maxHeartbeats 1000000 in
theorem solution {m : W} (f : Lp ℂ 2 (volume : Measure W)) :
    f ∈ momDomain m ↔ ∃ g, IsMomInverse m f g := Iff.rfl
