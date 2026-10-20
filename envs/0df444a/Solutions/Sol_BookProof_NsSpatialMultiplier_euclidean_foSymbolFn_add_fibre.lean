-- Prove2me | solution 1 for BookProof.NsSpatialMultiplier.euclidean_foSymbolFn_add_fibre
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T15:09:23.11778+00:00
-- url     : https://prove2.me/submissions/3db04efb-d414-4623-9965-6fa85f654754

-- Generated from ChapterNsSpatialMomentumMultiplier.lean — theorem BookProof.NsSpatialMultiplier.euclidean_foSymbolFn_add_fibre
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
theorem solution {n : ℕ} (c : ι → ℝ) (s : ι → Fin n) (j : Fin n)
    (hj : ∀ i, s i ≠ j) (x : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    foSymbolFn c (fun i => EuclideanSpace.single (s i) (1 : ℝ))
        (x + t • EuclideanSpace.single j (1 : ℝ))
      = foSymbolFn c (fun i => EuclideanSpace.single (s i) (1 : ℝ)) x := by 
  unfold foSymbolFn
  apply Finset.sum_congr rfl
  intro i _
  rw [inner_add_left, inner_smul_left, EuclideanSpace.inner_single_left]
  simp [EuclideanSpace.single_apply, Ne.symm (hj i)]
