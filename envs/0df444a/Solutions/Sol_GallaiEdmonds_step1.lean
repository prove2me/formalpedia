-- Prove2me | solution 1 for GallaiEdmonds.step1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:02:18.092399+00:00
-- url     : https://prove2.me/submissions/f83bda4d-0d1f-4265-b47d-94eaedfba5e3

module
public import Mathlib
public import Definitions.Def_BergeLib_Berge
public import Definitions.Def_GallaiEdmondsLib_GEComponents
public import Definitions.Def_GallaiEdmondsLib_GEMatching
public import Theorems.Thm_GallaiEdmonds_even_ncard_verts
public import Theorems.Thm_GallaiEdmonds_partner_adj
public import Theorems.Thm_GallaiEdmonds_comps_eq_cc
public import Theorems.Thm_GallaiEdmonds_comps_subset
public import Theorems.Thm_GallaiEdmonds_mem_cc_of_adj
public import Theorems.Thm_GallaiEdmonds_mem_cc_self


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open GallaiEdmonds
variable {V : Type*} {G : SimpleGraph V}
namespace GallaiEdmonds
theorem _root_.solution [Finite V] {M : G.Subgraph} (hM : M.IsMatching) {U : Set V}
    (hEq : M.verts.ncard + oddC G Uᶜ = Nat.card V + U.ncard) :
    (∀ u ∈ U, ∃ x, M.Adj u x ∧ x ∉ U ∧ Odd (cc G Uᶜ x).ncard) ∧
    (∀ u ∈ U, ∀ u' ∈ U, ∀ x x', u ≠ u' → M.Adj u x → M.Adj u' x' →
      cc G Uᶜ x ≠ cc G Uᶜ x') ∧
    (∀ K ∈ oddComps G Uᶜ, ∀ y ∈ K, ∀ z ∈ K, y ≠ z →
      (∃ w ∈ K, M.Adj y w) ∨ (∃ w ∈ K, M.Adj z w)) ∧
    (∀ y, y ∉ U → Even (cc G Uᶜ y).ncard → ∃ w ∈ cc G Uᶜ y, M.Adj y w) := by
  classical
  set B : Set V := {y | y ∉ U ∧ ¬∃ w ∈ cc G Uᶜ y, M.Adj y w} with hB
  have hP : ∀ K ∈ oddComps G Uᶜ, ∃ y ∈ K, y ∈ B := by
    intro K hK
    by_contra hcon
    push Not at hcon
    have hall : ∀ y ∈ K, ∃ w ∈ K, M.Adj y w := by
      intro y hy
      have h := hcon y hy
      simp only [hB, Set.mem_ofPred_eq, not_and, not_not] at h
      obtain ⟨w, hw, hadj⟩ := h (comps_subset hK.1 hy)
      exact ⟨w, by rwa [← comps_eq_cc hK.1 hy] at hw, hadj⟩
    have hMK : (M.induce K).IsMatching := by
      intro y hy
      obtain ⟨w, hw, hadj⟩ := hall y hy
      exact ⟨w, ⟨hy, hw, hadj⟩, fun w' h => hM.eq_of_adj_left h.2.2 hadj⟩
    have := even_ncard_verts hMK
    rw [Subgraph.induce_verts] at this
    exact (Nat.not_even_iff_odd.mpr hK.2) this
  -- lower bound
  have hsubimg : oddComps G Uᶜ ⊆ cc G Uᶜ '' B := by
    intro K hK
    obtain ⟨y, hyK, hyB⟩ := hP K hK
    exact ⟨y, hyB, (comps_eq_cc hK.1 hyK).symm⟩
  have hlow1 := Set.ncard_le_ncard hsubimg
  have hlow2 : (cc G Uᶜ '' B).ncard ≤ B.ncard := Set.ncard_image_le
  -- upper bound
  have hB1 : B \ M.verts ⊆ M.vertsᶜ ∩ Uᶜ := fun y hy => ⟨hy.2, hy.1.1⟩
  have hpmaps : ∀ y ∈ B ∩ M.verts, partner hM y ∈ U ∩ M.verts := by
    intro y hy
    have hadj := partner_adj hM hy.2
    refine ⟨?_, M.edge_vert hadj.symm⟩
    by_contra hU
    exact hy.1.2 ⟨_, mem_cc_of_adj (mem_cc_self hy.1.1) hU (M.adj_sub hadj), hadj⟩
  have hpinj : Set.InjOn (partner hM) (B ∩ M.verts) := by
    intro y hy z hz hyz
    have hy' := partner_adj hM hy.2
    have hz' := partner_adj hM hz.2
    rw [hyz] at hy'
    exact hM.eq_of_adj_right hy' hz'
  have hpimg : partner hM '' (B ∩ M.verts) ⊆ U ∩ M.verts := by
    rintro _ ⟨y, hy, rfl⟩; exact hpmaps y hy
  have hB2 : (B ∩ M.verts).ncard ≤ (U ∩ M.verts).ncard := by
    rw [← hpinj.ncard_image]; exact Set.ncard_le_ncard hpimg
  have hBsplit := Set.ncard_inter_add_ncard_sdiff_eq_ncard B M.verts
  have hB1le := Set.ncard_le_ncard hB1
  -- global counting
  have c1 := Set.ncard_add_ncard_compl M.verts
  have c2 := Set.ncard_inter_add_ncard_sdiff_eq_ncard M.vertsᶜ U
  have c3 := Set.ncard_inter_add_ncard_sdiff_eq_ncard U M.verts
  have e1 : M.vertsᶜ \ U = M.vertsᶜ ∩ Uᶜ := rfl
  have e2 : U \ M.verts = M.vertsᶜ ∩ U :=
    Set.ext fun _ => ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  rw [e1] at c2
  rw [e2] at c3
  unfold oddC at hEq
  have hzero : (M.vertsᶜ ∩ U).ncard = 0 := by omega
  have hUM : U ⊆ M.verts := by
    intro u hu
    by_contra h
    rw [Set.ncard_eq_zero] at hzero
    exact (Set.eq_empty_iff_forall_notMem.mp hzero) u ⟨h, hu⟩
  -- consequences
  have himgeq : cc G Uᶜ '' B = oddComps G Uᶜ :=
    (Set.eq_of_subset_of_ncard_le hsubimg (by omega)).symm
  have hBodd : ∀ y ∈ B, Odd (cc G Uᶜ y).ncard := by
    intro y hy
    have : cc G Uᶜ y ∈ oddComps G Uᶜ := himgeq ▸ ⟨y, hy, rfl⟩
    exact this.2
  have hBinj : Set.InjOn (cc G Uᶜ) B := Set.injOn_of_ncard_image_eq (by omega)
  have hpsurj : partner hM '' (B ∩ M.verts) = U ∩ M.verts := by
    refine Set.eq_of_subset_of_ncard_le hpimg ?_
    rw [hpinj.ncard_image]; omega
  have hUB : ∀ u ∈ U, ∀ x, M.Adj u x → x ∈ B := by
    intro u hu x hx
    have : u ∈ partner hM '' (B ∩ M.verts) := hpsurj ▸ ⟨hu, hUM hu⟩
    obtain ⟨y, hy, rfl⟩ := this
    have := partner_adj hM hy.2
    rw [hM.eq_of_adj_left hx this.symm]
    exact hy.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u hu
    have hx := partner_adj hM (hUM hu)
    have hxB := hUB u hu _ hx
    exact ⟨_, hx, hxB.1, hBodd _ hxB⟩
  · intro u hu u' hu' x x' hne hx hx' hcc
    have hxx : x = x' := hBinj (hUB u hu x hx) (hUB u' hu' x' hx') hcc
    rw [hxx] at hx
    exact hne (hM.eq_of_adj_right hx hx')
  · intro K hK y hy z hz hne
    by_contra hcon
    push Not at hcon
    have hyB : y ∈ B := by
      refine ⟨comps_subset hK.1 hy, ?_⟩
      rw [← comps_eq_cc hK.1 hy]
      exact fun ⟨w, hw, h⟩ => hcon.1 w hw h
    have hzB : z ∈ B := by
      refine ⟨comps_subset hK.1 hz, ?_⟩
      rw [← comps_eq_cc hK.1 hz]
      exact fun ⟨w, hw, h⟩ => hcon.2 w hw h
    exact hne (hBinj hyB hzB (by rw [← comps_eq_cc hK.1 hy, ← comps_eq_cc hK.1 hz]))
  · intro y hy heven
    by_contra hcon
    exact (Nat.not_even_iff_odd.mpr (hBodd y ⟨hy, hcon⟩)) heven
end GallaiEdmonds
