-- Prove2me | solution 1 for D1Bound5.card_bound_iff_no_ordered_sextuple
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T21:27:00.129204+00:00
-- url     : https://prove2.me/submissions/95afb5a3-e544-4864-b9f6-6dba640f377b

import Definitions.Def_D1Bound5_IsD1
import Definitions.Def_D1Bound5_IsD1Tuple
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fintype.EquivFin

namespace D1Bound5

theorem IsD1.exists_ordered_sextuple {R W : Type*} [CommRing R] [LinearOrder W]
    {A : Finset R} (hA : IsD1 A) (hcard : 5 < A.card) (weight : R → W) :
    ∃ f : Fin 6 → R, IsD1Tuple f ∧ (∀ i, f i ∈ A) ∧ Monotone (weight ∘ f) := by
  classical
  obtain ⟨B, hBA, hB⟩ := Finset.exists_subset_card_eq (show 6 ≤ A.card by omega)
  let e : Fin 6 ≃ B := (Fintype.equivFinOfCardEq (by simpa using hB)).symm
  let f0 : Fin 6 → R := fun i => (e i).val
  have hi0 : Function.Injective f0 := by
    intro i j h
    apply e.injective
    exact Subtype.ext h
  let σ := Tuple.sort (weight ∘ f0)
  let f : Fin 6 → R := f0 ∘ σ
  have hi : Function.Injective f := hi0.comp σ.injective
  have hm : ∀ i, f i ∈ A := fun i => hBA (e (σ i)).property
  refine ⟨f, ⟨hi, ?_, ?_⟩, hm, ?_⟩
  · exact fun i => hA.1 (f i) (hm i)
  · exact fun i j hij => hA.2 (f i) (hm i) (f j) (hm j)
      (fun h => hij (hi h))
  · exact Tuple.monotone_sort (weight ∘ f0)

theorem IsD1Tuple.isD1_image {R : Type*} [CommRing R] [DecidableEq R]
    {n : ℕ} {f : Fin n → R} (hf : IsD1Tuple f) :
    IsD1 (Finset.univ.image f) := by
  constructor
  · intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact hf.2.1 i
  · intro x hx y hy hxy
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hy
    exact hf.2.2 i j (fun h => hxy (congrArg f h))

theorem IsD1Tuple.card_image {R : Type*} [CommRing R] [DecidableEq R]
    {n : ℕ} {f : Fin n → R} (hf : IsD1Tuple f) :
    (Finset.univ.image f).card = n := by
  rw [Finset.card_image_of_injective _ hf.1]
  exact Finset.card_fin n

theorem _root_.solution {R W : Type*} [CommRing R] [LinearOrder W]
    (weight : R → W) :
    (∀ A : Finset R, IsD1 A → A.card ≤ 5) ↔
      ∀ f : Fin 6 → R, IsD1Tuple f → Monotone (weight ∘ f) → False := by
  classical
  constructor
  · intro h f hf _
    have hle := h (Finset.univ.image f) hf.isD1_image
    have hc := hf.card_image
    omega
  · intro h A hA
    by_contra hle
    obtain ⟨f, hf, _, hs⟩ := hA.exists_ordered_sextuple (by omega) weight
    exact h f hf hs

end D1Bound5
