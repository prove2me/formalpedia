-- Prove2me | solution 1 for BookProof.ChapterSolovayCoordinates.infinitePi_map_sumPiEquivProdPi
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-21T16:00:29.75929+00:00
-- url     : https://prove2.me/submissions/42620de4-b3cc-46f5-b2db-92326d345410

-- Generated from ChapterSolovayCoordinates.lean — solution of BookProof.ChapterSolovayCoordinates.infinitePi_map_sumPiEquivProdPi
import Mathlib
import Definitions.Def_ChapterSolovayCoordinates
import Theorems.Thm_BookProof_ChapterSolovayCoordinates_infinitePi_map_sumPiEquivProdPi_symm
open BookProof.ChapterSolovayCoordinates



open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution {ι ι' : Type*} [Fintype ι] {X : ι ⊕ ι' → Type*}
    [∀ i, MeasurableSpace (X i)] (mu : ∀ i, Measure (X i))
    [∀ i, IsProbabilityMeasure (mu i)] :
    Measure.map (MeasurableEquiv.sumPiEquivProdPi X) (Measure.infinitePi mu)
      = (Measure.pi fun i : ι => mu (Sum.inl i)).prod
        (Measure.infinitePi fun j : ι' => mu (Sum.inr j)) := by

  rw [← Measure.infinitePi_eq_pi]
  exact (MeasurableEquiv.map_apply_eq_iff_map_symm_apply_eq _).2
    (infinitePi_map_sumPiEquivProdPi_symm mu).symm
