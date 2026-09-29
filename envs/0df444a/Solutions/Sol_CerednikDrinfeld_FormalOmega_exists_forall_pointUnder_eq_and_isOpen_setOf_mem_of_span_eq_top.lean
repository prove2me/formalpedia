-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.exists_forall_pointUnder_eq_and_isOpen_setOf_mem_of_span_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/711583e6-c017-536e-922e-50fb4b654b66

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadrupleRelations
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_exists_forall_pointUnder_eq_and_isOpen_setOf_mem_of_span_eq_top

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

namespace B24X4c

variable {𝒪 : Type} [CommRing 𝒪] {B : Type} [CommRing B] [Algebra 𝒪 B]

theorem pointUnder_toAlgHom (C : Type) [CommRing C] [Algebra 𝒪 C] [Algebra B C] [IsScalarTower 𝒪 B C]
    (y : PrimeSpectrum C) :
    DrinfeldDatum.pointUnder (IsScalarTower.toAlgHom 𝒪 B C) y = PrimeSpectrum.comap (algebraMap B C) y := rfl

theorem exists_not_mem {k : ℕ} (f : Fin k → B) (hf : Ideal.span (Set.range f) = ⊤) (x : PrimeSpectrum B) :
    ∃ i : Fin k, f i ∉ x.asIdeal := by
  by_contra h
  push_neg at h
  apply x.isPrime.ne_top
  rw [eq_top_iff, ← hf]
  exact Ideal.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact h i)

end B24X4c

open B24X4c in
theorem solution
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
    {B : Type} [CommRing B] [Algebra 𝒪 B] {k : ℕ} (f : Fin k → B) (hf : Ideal.span (Set.range f) = ⊤)
    (N : ∀ i : Fin k, PrimeSpectrum (Localization.Away (f i)) → Submodule 𝒪 (Fin 2 → K))
    (hN : ∀ (i : Fin k) (v : Fin 2 → K), IsOpen {y : PrimeSpectrum (Localization.Away (f i)) | v ∈ N i y})
    (hcompat : ∀ (i j : Fin k) (y : PrimeSpectrum (Localization.Away (f i))) (z : PrimeSpectrum (Localization.Away (f j))),
      DrinfeldDatum.pointUnder (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i))) y =
        DrinfeldDatum.pointUnder (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f j))) z → N i y = N j z) :
    ∃ Ng : PrimeSpectrum B → Submodule 𝒪 (Fin 2 → K),
      (∀ (i : Fin k) (y : PrimeSpectrum (Localization.Away (f i))),
          Ng (DrinfeldDatum.pointUnder (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i))) y) = N i y) ∧
      ∀ v : Fin 2 → K, IsOpen {x : PrimeSpectrum B | v ∈ Ng x} := by
  classical
  have cover : ∀ x : PrimeSpectrum B, ∃ (i : Fin k) (y : PrimeSpectrum (Localization.Away (f i))),
      DrinfeldDatum.pointUnder (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i))) y = x := by
    intro x
    obtain ⟨i, hi⟩ := exists_not_mem f hf x
    have hx : x ∈ Set.range (PrimeSpectrum.comap (algebraMap B (Localization.Away (f i)))) := by
      rw [PrimeSpectrum.localization_away_comap_range _ (f i)]
      exact hi
    obtain ⟨y, hy⟩ := hx
    exact ⟨i, y, by rw [pointUnder_toAlgHom]; exact hy⟩
  choose ι υ hιυ using cover
  refine ⟨fun x => N (ι x) (υ x), fun i y => hcompat _ _ _ _ (hιυ _), fun v => ?_⟩
  have hset : {x : PrimeSpectrum B | v ∈ N (ι x) (υ x)} =
      ⋃ i, PrimeSpectrum.comap (algebraMap B (Localization.Away (f i))) ''
        {y : PrimeSpectrum (Localization.Away (f i)) | v ∈ N i y} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_image]
    constructor
    · intro hv
      exact ⟨ι x, υ x, hv, by rw [← pointUnder_toAlgHom (𝒪 := 𝒪)]; exact hιυ x⟩
    · rintro ⟨i, y, hy, rfl⟩
      have key := hcompat (ι _) i (υ _) y (by rw [hιυ, pointUnder_toAlgHom])
      show v ∈ N (ι _) (υ _)
      rw [key]
      exact hy
  rw [hset]
  exact isOpen_iUnion fun i =>
    (PrimeSpectrum.localization_away_isOpenEmbedding (Localization.Away (f i)) (f i)).isOpenMap _ (hN i v)

end S_CerednikDrinfeld_FormalOmega_exists_forall_pointUnder_eq_and_isOpen_setOf_mem_of_span_eq_top
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_exists_forall_pointUnder_eq_and_isOpen_setOf_mem_of_span_eq_top (solution)
