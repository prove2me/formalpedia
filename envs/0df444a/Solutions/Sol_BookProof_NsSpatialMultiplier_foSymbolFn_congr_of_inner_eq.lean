-- Prove2me | solution 1 for BookProof.NsSpatialMultiplier.foSymbolFn_congr_of_inner_eq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T08:20:30.153588+00:00
-- url     : https://prove2.me/submissions/96f921f2-866a-4266-a1f7-3b8c196b8553

-- Generated from ChapterNsSpatialMomentumMultiplier.lean — solution of BookProof.NsSpatialMultiplier.foSymbolFn_congr_of_inner_eq
import Mathlib
import Definitions.Def_ChapterNsSpatialMomentumMultiplier
import Definitions.Def_ChapterStrichartzWave
import Definitions.Def_ChapterFourierMultiplierEsa
open BookProof.NsSpatialMultiplier




open MeasureTheory SchwartzMap FourierTransform
open BookProof.StrichartzWave BookProof.FourierMultiplierEsa

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {ι : Type*} [Fintype ι]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {ι : Type*} [Fintype ι]
variable (V) in

set_option maxHeartbeats 1000000 in
theorem solution (c : ι → ℝ) (w : ι → V) {x y : V}
    (h : ∀ i, (inner ℝ x (w i) : ℝ) = inner ℝ y (w i)) :
    foSymbolFn c w x = foSymbolFn c w y := Finset.sum_congr rfl fun i _ => by rw [h i]
