-- Prove2me | solution 1 for GallaiEdmonds.minBarrier_surplus
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:08:44.660242+00:00
-- url     : https://prove2.me/submissions/ad7019ee-d0c5-430c-beda-74be1f53fa7f

module
public import Mathlib
public import Definitions.Def_BergeLib_Berge
public import Definitions.Def_GallaiEdmondsLib_GEMatching
public import Definitions.Def_GallaiEdmondsLib_GEBarrier
public import Theorems.Thm_GallaiEdmonds_IsBarrier_eq
public import Theorems.Thm_GallaiEdmonds_isBarrier_of_le
public import Theorems.Thm_GallaiEdmonds_cc_eq_of_closed
public import Theorems.Thm_GallaiEdmonds_cc_mem_comps
public import Theorems.Thm_GallaiEdmonds_comps_closed
public import Theorems.Thm_GallaiEdmonds_comps_eq_cc
public import Theorems.Thm_GallaiEdmonds_comps_eq_of_mem
public import Theorems.Thm_GallaiEdmonds_comps_nonempty
public import Theorems.Thm_GallaiEdmonds_comps_subset
public import Theorems.Thm_GallaiEdmonds_mem_cc_self
public import Theorems.Thm_GallaiEdmonds_partner_eq
public import Theorems.Thm_GallaiEdmonds_step1


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
    {v : V} (hv : v ∈ oddPart G U) {s : Set V} (hs : s ⊆ U) :
    s.ncard ≤
      {K | K ∈ oddComps G Uᶜ ∧ K ≠ cc G Uᶜ v ∧ ∃ u ∈ s, ∃ x ∈ K, G.Adj u x}.ncard := by
  by_contra hlt
  push Not at hlt
  set K0 := cc G Uᶜ v with hK0
  set N := {K | K ∈ oddComps G Uᶜ ∧ ∃ u ∈ s, ∃ x ∈ K, G.Adj u x} with hNdef
  set N' := {K | K ∈ oddComps G Uᶜ ∧ K ≠ K0 ∧ ∃ u ∈ s, ∃ x ∈ K, G.Adj u x} with hN'def
  have heq := hU.1.eq hM hmax
  obtain ⟨h1a, h1b, -, -⟩ := step1 hM heq
  have hsN : s.ncard ≤ N.ncard := by
    refine Set.ncard_le_ncard_of_injOn (fun u => cc G Uᶜ (partner hM u)) ?_ ?_
    · intro u hu
      obtain ⟨x, hx, hxU, hodd⟩ := h1a u (hs hu)
      simp only [partner_eq hM hx]
      exact ⟨⟨cc_mem_comps hxU, hodd⟩, u, hu, x, mem_cc_self hxU, M.adj_sub hx⟩
    · intro u hu u' hu' h
      by_contra hne
      obtain ⟨x, hx, -⟩ := h1a u (hs hu)
      obtain ⟨x', hx', -⟩ := h1a u' (hs hu')
      simp only [partner_eq hM hx, partner_eq hM hx'] at h
      exact h1b u (hs hu) u' (hs hu') x x' hne hx hx' h
  have hNsub : N ⊆ insert K0 N' := by
    rintro K ⟨hK, hadj⟩
    by_cases h : K = K0
    · exact Or.inl h
    · exact Or.inr ⟨hK, h, hadj⟩
  have hK0N : K0 ∈ N := by
    by_contra hK0
    have : N ⊆ N' := fun K hK => ⟨hK.1, fun h => hK0 (h ▸ hK), hK.2⟩
    have := Set.ncard_le_ncard this
    omega
  have hNle : N.ncard ≤ N'.ncard + 1 :=
    (Set.ncard_le_ncard hNsub).trans (Set.ncard_insert_le _ _)
  set U' := U \ s with hU'
  set Q := oddComps G Uᶜ \ N with hQ
  have hQsub : Q ⊆ oddComps G U'ᶜ := by
    rintro K ⟨hK, hKN⟩
    obtain ⟨x, hx⟩ := comps_nonempty hK.1
    have hKU' : K ⊆ U'ᶜ := fun y hy hyU' => comps_subset hK.1 hy hyU'.1
    have hcl : Closed G U'ᶜ K := by
      intro y hy z hz hadj
      by_cases hzU : z ∈ U
      · exfalso
        have hzs : z ∈ s := by
          by_contra h
          exact hz ⟨hzU, h⟩
        exact hKN ⟨hK, z, hzs, y, hy, hadj.symm⟩
      · exact comps_closed hK.1 y hy z hzU hadj
    refine ⟨⟨x, hKU' hx, ?_⟩, hK.2⟩
    rw [← cc_eq_of_closed hKU' hcl hx,
      cc_eq_of_closed (comps_subset hK.1) (comps_closed hK.1) hx, comps_eq_cc hK.1 hx]
  have hNodd : N ⊆ oddComps G Uᶜ := fun K hK => hK.1
  have hQcard : Q.ncard + N.ncard = (oddComps G Uᶜ).ncard :=
    Set.ncard_sdiff_add_ncard_of_subset hNodd
  have hU'card : U'.ncard + s.ncard = U.ncard := Set.ncard_sdiff_add_ncard_of_subset hs
  have hQle := Set.ncard_le_ncard hQsub
  unfold oddC at heq
  have hU'bar : IsBarrier G U' := isBarrier_of_le hM (by unfold oddC; omega)
  have heq' := hU'bar.eq hM hmax
  unfold oddC at heq'
  have hQeq : Q = oddComps G U'ᶜ := Set.eq_of_subset_of_ncard_le hQsub (by omega)
  have hsubOP : oddPart G U' ⊆ oddPart G U \ K0 := by
    rintro y ⟨hyU', hyodd⟩
    have hK : cc G U'ᶜ y ∈ Q := hQeq ▸ ⟨cc_mem_comps hyU', hyodd⟩
    have hyK : y ∈ cc G U'ᶜ y := mem_cc_self hyU'
    have hyUc : y ∈ Uᶜ := comps_subset hK.1.1 hyK
    have hcc : cc G U'ᶜ y = cc G Uᶜ y := comps_eq_cc hK.1.1 hyK
    refine ⟨⟨hyUc, ?_⟩, fun hyK0 => ?_⟩
    · rw [← hcc]; exact hK.1.2
    · have : cc G U'ᶜ y = K0 := comps_eq_of_mem hK.1.1 (cc_mem_comps hv.1) hyK hyK0
      exact hK.2 (this ▸ hK0N)
  have hvK0 : v ∈ K0 := mem_cc_self hv.1
  have h1 := Set.ncard_le_ncard hsubOP
  have h2 : (oddPart G U \ K0).ncard < (oddPart G U).ncard :=
    Set.ncard_lt_ncard (Set.ssubset_iff_subset_ne.mpr ⟨Set.sdiff_subset,
      fun h => (by rw [h]; exact hv : v ∈ oddPart G U \ K0).2 hvK0⟩)
  have h3 := hU.2 U' hU'bar
  omega
end GallaiEdmonds
