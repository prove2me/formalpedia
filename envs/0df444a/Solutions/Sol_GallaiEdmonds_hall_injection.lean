-- Prove2me | solution 1 for GallaiEdmonds.hall_injection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:10:00.523225+00:00
-- url     : https://prove2.me/submissions/8315ec4f-340b-43cd-a740-00e47149eb8a

module
public import Mathlib
public import Definitions.Def_BergeLib_Berge
public import Definitions.Def_GallaiEdmondsLib_GEBarrier
public import Definitions.Def_GallaiEdmondsLib_GEConstruct
public import Theorems.Thm_GallaiEdmonds_minBarrier_surplus


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open GallaiEdmonds
variable {V : Type*} {G : SimpleGraph V}
namespace GallaiEdmonds
theorem _root_.solution [Finite V] {U : Set V} (hU : IsMinBarrier G U)
    {M : G.Subgraph} (hM : M.IsMatching)
    (hmax : ∀ N : G.Subgraph, N.IsMatching → N.edgeSet.ncard ≤ M.edgeSet.ncard)
    {v : V} (hv : v ∈ oddPart G U) :
    ∃ f : V → Set V,
      (∀ u ∈ U, f u ∈ oddComps G Uᶜ ∧ f u ≠ cc G Uᶜ v ∧ ∃ x ∈ f u, G.Adj u x) ∧
      Set.InjOn f U := by
  classical
  let P : V → Set (Set V) :=
    fun u => {K | K ∈ oddComps G Uᶜ ∧ K ≠ cc G Uᶜ v ∧ ∃ x ∈ K, G.Adj u x}
  let t : U → Finset (Set V) := fun u => (Set.toFinite (P u.1)).toFinset
  have hall : ∀ s : Finset U, s.card ≤ (s.biUnion t).card := by
    intro s
    have h := minBarrier_surplus hU hM hmax hv (s := Subtype.val '' (s : Set U))
      (by rintro _ ⟨u, -, rfl⟩; exact u.2)
    have e1 : (Subtype.val '' (s : Set U)).ncard = s.card := by
      rw [Set.ncard_image_of_injective _ Subtype.val_injective, Set.ncard_coe_finset]
    have e2 : ((s.biUnion t : Finset (Set V)) : Set (Set V)) =
        {K | K ∈ oddComps G Uᶜ ∧ K ≠ cc G Uᶜ v ∧
          ∃ u ∈ Subtype.val '' (s : Set U), ∃ x ∈ K, G.Adj u x} := by
      ext K
      simp only [Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe, Set.Finite.mem_toFinset,
        t, P, Set.mem_ofPred_eq, Set.mem_image]
      constructor
      · rintro ⟨u, hu, hK, hne, x, hx, hadj⟩
        exact ⟨hK, hne, u, ⟨u, hu, rfl⟩, x, hx, hadj⟩
      · rintro ⟨hK, hne, _, ⟨u, hu, rfl⟩, x, hx, hadj⟩
        exact ⟨u, hu, hK, hne, x, hx, hadj⟩
    rw [← Set.ncard_coe_finset (s.biUnion t), e2, ← e1]
    exact h
  obtain ⟨g, hginj, hgt⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective t).mp hall
  refine ⟨fun u => if h : u ∈ U then g ⟨u, h⟩ else ∅, ?_, ?_⟩
  · intro u hu
    simp only [hu, ↓reduceDIte]
    have := hgt ⟨u, hu⟩
    simp only [t, Set.Finite.mem_toFinset] at this
    exact this
  · intro u hu u' hu' h
    simp only [hu, hu', ↓reduceDIte] at h
    exact congrArg Subtype.val (hginj h)
end GallaiEdmonds
