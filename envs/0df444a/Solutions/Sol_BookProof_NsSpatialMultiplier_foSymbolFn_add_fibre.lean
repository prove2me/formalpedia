-- Prove2me | solution 1 for BookProof.NsSpatialMultiplier.foSymbolFn_add_fibre
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T15:09:15.834077+00:00
-- url     : https://prove2.me/submissions/e11b8e07-0376-449f-ab0e-4d8d017234a3

-- Generated from ChapterNsSpatialMomentumMultiplier.lean — theorem BookProof.NsSpatialMultiplier.foSymbolFn_add_fibre
import Definitions.Def_ChapterStrichartzWave
import Mathlib
import Definitions.Def_ChapterNsSpatialMomentumMultiplier
import Definitions.Def_ChapterFourierMultiplierEsa
open BookProof.FourierMultiplierEsa
open BookProof.NsSpatialMultiplier



open MeasureTheory SchwartzMap FourierTransform
open BookProof.StrichartzWave BookProof.FourierMultiplierEsa

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {ι : Type*} [Fintype ι]

variable (V) in
theorem solution (c : ι → ℝ) (w : ι → V) (x m : V)
    (hm : ∀ i, (inner ℝ m (w i) : ℝ) = 0) (t : ℝ) :
    foSymbolFn c w (x + t • m) = foSymbolFn c w x := by 
  unfold foSymbolFn
  apply Finset.sum_congr rfl
  intro i _
  rw [inner_add_left, inner_smul_left, hm i]
  simp
