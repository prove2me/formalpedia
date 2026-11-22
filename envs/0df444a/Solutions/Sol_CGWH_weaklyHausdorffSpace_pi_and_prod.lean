-- Prove2me | solution 1 for CGWH.weaklyHausdorffSpace_pi_and_prod
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T15:29:37.599638+00:00
-- url     : https://prove2.me/submissions/44d1887a-4df6-407c-b97b-1eddaa9af978

import Definitions.Def_CGWH_WeakHausdorff
import Theorems.Thm_CGWH_t2Space_of_surjective_of_compactSpace_t2Space

open Topology TopologicalSpace

set_option autoImplicit false

universe u

open CGWH

namespace Sol_CGWH_weaklyHausdorffSpace_pi_and_prod

/-- A subspace of a weakly Hausdorff space is weakly Hausdorff. -/
theorem wh_subtype (X : Type u) [TopologicalSpace X] [WeaklyHausdorffSpace X] (s : Set X) :
    WeaklyHausdorffSpace s := by
  refine ⟨fun K _ _ _ f hf => ?_⟩
  have h := WeaklyHausdorffSpace.isClosed_range K (fun k => (f k : X))
    (continuous_subtype_val.comp hf)
  have : Set.range f = Subtype.val ⁻¹' (Set.range fun k => (f k : X)) := by
    ext y; constructor
    · rintro ⟨k, rfl⟩; exact ⟨k, rfl⟩
    · rintro ⟨k, hk⟩; exact ⟨k, Subtype.ext hk⟩
  rw [this]; exact h.preimage continuous_subtype_val

theorem pi_case (ι : Type u) (X : ι → Type u) [∀ i, TopologicalSpace (X i)]
    [∀ i, WeaklyHausdorffSpace (X i)] : WeaklyHausdorffSpace (∀ i, X i) := by
  refine ⟨fun K _ _ _ g hg => ?_⟩
  let C : ∀ i, Set (X i) := fun i => Set.range (fun k => g k i)
  have hgi : ∀ i, Continuous (fun k => g k i) := fun i => (continuous_apply i).comp hg
  have hCcl : ∀ i, IsClosed (C i) := fun i =>
    WeaklyHausdorffSpace.isClosed_range K _ (hgi i)
  have hT2 : ∀ i, T2Space (C i) := fun i => by
    haveI := wh_subtype (X i) (C i)
    exact CGWH.t2Space_of_surjective_of_compactSpace_t2Space
      (q := Set.rangeFactorization (fun k => g k i))
      ((hgi i).subtype_mk _) Set.rangeFactorization_surjective
  let g' : K → ∀ i, C i := fun k i => ⟨g k i, k, rfl⟩
  have hg' : Continuous g' := continuous_pi fun i => (hgi i).subtype_mk _
  have hr : IsClosed (Set.range g') := (isCompact_range hg').isClosed
  let φ : (∀ i, C i) → (∀ i, X i) := Pi.map (fun i => (Subtype.val : C i → X i))
  have hφ : IsClosedEmbedding φ :=
    IsClosedEmbedding.piMap fun i => (hCcl i).isClosedEmbedding_subtypeVal
  have : Set.range g = φ '' Set.range g' := by
    rw [← Set.range_comp]; rfl
  rw [this]; exact hφ.isClosedMap _ hr

theorem prod_case (X Y : Type u) [TopologicalSpace X] [TopologicalSpace Y]
    [WeaklyHausdorffSpace X] [WeaklyHausdorffSpace Y] : WeaklyHausdorffSpace (X × Y) := by
  refine ⟨fun K _ _ _ g hg => ?_⟩
  have h1 : Continuous (fun k => (g k).1) := continuous_fst.comp hg
  have h2 : Continuous (fun k => (g k).2) := continuous_snd.comp hg
  let C : Set X := Set.range (fun k => (g k).1)
  let D : Set Y := Set.range (fun k => (g k).2)
  have hC : IsClosed C := WeaklyHausdorffSpace.isClosed_range K _ h1
  have hD : IsClosed D := WeaklyHausdorffSpace.isClosed_range K _ h2
  haveI : T2Space C := by
    haveI := wh_subtype X C
    exact CGWH.t2Space_of_surjective_of_compactSpace_t2Space
      (q := Set.rangeFactorization (fun k => (g k).1))
      (h1.subtype_mk _) Set.rangeFactorization_surjective
  haveI : T2Space D := by
    haveI := wh_subtype Y D
    exact CGWH.t2Space_of_surjective_of_compactSpace_t2Space
      (q := Set.rangeFactorization (fun k => (g k).2))
      (h2.subtype_mk _) Set.rangeFactorization_surjective
  let g' : K → C × D := fun k => (⟨(g k).1, k, rfl⟩, ⟨(g k).2, k, rfl⟩)
  have hg' : Continuous g' := (h1.subtype_mk _).prodMk (h2.subtype_mk _)
  have hr : IsClosed (Set.range g') := (isCompact_range hg').isClosed
  have hφ : IsClosedEmbedding (Prod.map (Subtype.val : C → X) (Subtype.val : D → Y)) :=
    hC.isClosedEmbedding_subtypeVal.prodMap hD.isClosedEmbedding_subtypeVal
  have : Set.range g = Prod.map (Subtype.val : C → X) (Subtype.val : D → Y) '' Set.range g' := by
    rw [← Set.range_comp]; rfl
  rw [this]; exact hφ.isClosedMap _ hr

end Sol_CGWH_weaklyHausdorffSpace_pi_and_prod

theorem solution :
    (∀ (ι : Type u) (X : ι → Type u) [∀ i, TopologicalSpace (X i)]
        [∀ i, WeaklyHausdorffSpace (X i)], WeaklyHausdorffSpace (∀ i, X i)) ∧
      (∀ (X Y : Type u) [TopologicalSpace X] [TopologicalSpace Y]
        [WeaklyHausdorffSpace X] [WeaklyHausdorffSpace Y], WeaklyHausdorffSpace (X × Y)) :=
  ⟨fun ι X _ _ => Sol_CGWH_weaklyHausdorffSpace_pi_and_prod.pi_case ι X,
    fun X Y _ _ _ _ => Sol_CGWH_weaklyHausdorffSpace_pi_and_prod.prod_case X Y⟩
