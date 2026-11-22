-- Prove2me | solution 1 for CGSpace.cocountable_not_compactlyGenerated
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T11:54:00.823333+00:00
-- url     : https://prove2.me/submissions/0949b621-9a05-4922-86b8-7a1539bc104d

import Mathlib

open Topology TopologicalSpace

set_option autoImplicit false

universe u v

namespace Sol_CGSpace_cocountable_not_compactlyGenerated

/-- In the co-countable topology, every countable subset is discrete. -/
lemma isDiscrete_of_countable {X : Type u} [TopologicalSpace X]
    (h : ∀ s : Set X, IsClosed s ↔ s = Set.univ ∨ s.Countable)
    {A : Set X} (hA : A.Countable) : IsDiscrete A := by
  rw [isDiscrete_iff_forall_mem_exists_isClosed]
  intro s hs
  exact ⟨s, (h s).2 (Or.inr (hA.mono hs)), Set.inter_eq_left.2 hs⟩

/-- In the co-countable topology, every compact subset is finite. -/
lemma finite_of_isCompact {X : Type u} [TopologicalSpace X]
    (h : ∀ s : Set X, IsClosed s ↔ s = Set.univ ∨ s.Countable)
    {C : Set X} (hC : IsCompact C) : C.Finite := by
  by_contra hinf
  have hinf' : C.Infinite := hinf
  -- a countably infinite subset `A` of `C`
  let e : ℕ ↪ C := hinf'.natEmbedding C
  let A : Set X := Set.range fun n : ℕ => (e n : X)
  have hAC : A ⊆ C := by
    rintro _ ⟨n, rfl⟩
    exact (e n).2
  have hAcount : A.Countable := Set.countable_range _
  have hAinf : A.Infinite :=
    Set.infinite_range_of_injective (Subtype.val_injective.comp e.injective)
  -- `A` is closed in the compact set `C`, hence compact; it is discrete, hence finite
  have hAclosed : IsClosed A := (h A).2 (Or.inr hAcount)
  have hAcompact : IsCompact A := hC.of_isClosed_subset hAclosed hAC
  exact hAinf (hAcompact.finite (isDiscrete_of_countable h hAcount))

/-- For the co-countable topology, the preimage of an arbitrary subset under a continuous map
from a compact space is closed. -/
lemma isClosed_preimage_of_compactSpace {X : Type u} [TopologicalSpace X]
    (h : ∀ s : Set X, IsClosed s ↔ s = Set.univ ∨ s.Countable)
    {K : Type v} [TopologicalSpace K] [CompactSpace K] {g : K → X} (hg : Continuous g)
    (Z : Set X) : IsClosed (g ⁻¹' Z) := by
  have hfin : (Set.range g).Finite := finite_of_isCompact h (isCompact_range hg)
  have hclosed : IsClosed (Z ∩ Set.range g) :=
    (h _).2 (Or.inr (hfin.subset Set.inter_subset_right).countable)
  have heq : g ⁻¹' Z = g ⁻¹' (Z ∩ Set.range g) := by
    ext x
    simp
  rw [heq]
  exact hclosed.preimage hg

end Sol_CGSpace_cocountable_not_compactlyGenerated

open Sol_CGSpace_cocountable_not_compactlyGenerated in
theorem solution
    (X : Type u) [TopologicalSpace X] [Uncountable X]
    (h : ∀ s : Set X, IsClosed s ↔ s = Set.univ ∨ s.Countable) :
    TopologicalSpace.compactlyGenerated.{v} X = ⊥ ∧ ¬ UCompactlyGeneratedSpace.{v} X := by
  -- every subset of `X` is closed for the compactly generated topology
  have hkclosed : ∀ Z : Set X, IsClosed[TopologicalSpace.compactlyGenerated.{v} X] Z := by
    intro Z
    rw [TopologicalSpace.compactlyGenerated, isClosed_coinduced, isClosed_sigma_iff]
    rintro ⟨S, g⟩
    exact isClosed_preimage_of_compactSpace h g.continuous Z
  have hbot : TopologicalSpace.compactlyGenerated.{v} X = ⊥ := by
    rw [eq_bot_iff]
    intro s _
    have := (hkclosed sᶜ).isOpen_compl
    rwa [compl_compl] at this
  refine ⟨hbot, fun hcg => ?_⟩
  -- if `X` were compactly generated, every subset would be closed
  have hall : ∀ Z : Set X, IsClosed Z := by
    intro Z
    exact UCompactlyGeneratedSpace.isClosed.{v}
      (fun S g => isClosed_preimage_of_compactSpace h g.continuous Z)
  -- but the complement of a point is neither `univ` nor countable
  obtain ⟨x⟩ : Nonempty X := inferInstance
  rcases (h ({x}ᶜ : Set X)).1 (hall _) with h1 | h2
  · have : x ∈ ({x}ᶜ : Set X) := h1 ▸ Set.mem_univ x
    exact this rfl
  · have huniv : (Set.univ : Set X).Countable := by
      have : (Set.univ : Set X) = {x} ∪ {x}ᶜ := (Set.union_compl_self _).symm
      rw [this]
      exact (Set.countable_singleton x).union h2
    exact Set.not_countable_univ huniv
