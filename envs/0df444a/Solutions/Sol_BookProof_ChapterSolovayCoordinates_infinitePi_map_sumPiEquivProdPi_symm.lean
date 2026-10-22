-- Prove2me | solution 1 for BookProof.ChapterSolovayCoordinates.infinitePi_map_sumPiEquivProdPi_symm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-21T16:00:28.307308+00:00
-- url     : https://prove2.me/submissions/918cce3b-d659-47a9-a487-98ad8207729a

-- Generated from ChapterSolovayCoordinates.lean — solution of BookProof.ChapterSolovayCoordinates.infinitePi_map_sumPiEquivProdPi_symm
import Mathlib
import Definitions.Def_ChapterSolovayCoordinates
open BookProof.ChapterSolovayCoordinates



open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution {ι ι' : Type*} {X : ι ⊕ ι' → Type*}
    [∀ i, MeasurableSpace (X i)] (mu : ∀ i, Measure (X i))
    [∀ i, IsProbabilityMeasure (mu i)] :
    Measure.map (MeasurableEquiv.sumPiEquivProdPi X).symm
      ((Measure.infinitePi fun i : ι => mu (Sum.inl i)).prod
        (Measure.infinitePi fun j : ι' => mu (Sum.inr j))) = Measure.infinitePi mu := by

  refine Measure.eq_infinitePi _ fun s t ht => ?_
  rw [Measure.map_apply (MeasurableEquiv.measurable _)
    (MeasurableSet.pi s.countable_toSet fun _ _ => ht _)]
  have hpre : ⇑(MeasurableEquiv.sumPiEquivProdPi X).symm ⁻¹' ((s : Set (ι ⊕ ι')).pi t)
      = ((s.toLeft : Set ι).pi fun i => t (Sum.inl i)) ×ˢ
        ((s.toRight : Set ι').pi fun j => t (Sum.inr j)) := by
    ext ⟨a, b⟩
    have hL : ∀ i, (MeasurableEquiv.sumPiEquivProdPi X).symm (a, b) (Sum.inl i) = a i :=
      fun _ => rfl
    have hR : ∀ j, (MeasurableEquiv.sumPiEquivProdPi X).symm (a, b) (Sum.inr j) = b j :=
      fun _ => rfl
    constructor
    · intro h
      refine ⟨fun i hi => ?_, fun j hj => ?_⟩
      · simpa using hL i ▸ h (Sum.inl i) (by simpa using hi)
      · simpa using hR j ▸ h (Sum.inr j) (by simpa using hj)
    · rintro ⟨h1, h2⟩ i hi
      cases i with
      | inl i => simpa using (hL i).symm ▸ h1 i (by simpa using hi)
      | inr j => simpa using (hR j).symm ▸ h2 j (by simpa using hi)
  rw [hpre, Measure.prod_prod,
    Measure.infinitePi_pi (μ := fun i : ι => mu (Sum.inl i)) (s := s.toLeft)
      (t := fun i => t (Sum.inl i)) (fun i _ => ht _),
    Measure.infinitePi_pi (μ := fun j : ι' => mu (Sum.inr j)) (s := s.toRight)
      (t := fun j => t (Sum.inr j)) (fun j _ => ht _),
    Finset.prod_sum_eq_prod_toLeft_mul_prod_toRight s (fun i => mu i (t i))]
