-- Prove2me | solution 1 for DetDLP.w3_m5_lookup_subdivision
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-23T21:24:13.352799+00:00
-- url     : https://prove2.me/submissions/b75d851a-4575-4410-ae30-63929dd2cbc0

import Definitions.Def_DetDLP_TerminalBTN
import Definitions.Def_DetDLP_W4_M5Subdivision

set_option autoImplicit false
open DetDLP DetDLP.w4_M5Network

theorem solution (G : WireGraph) (L : Finset (Fin G.nV)) (m k S D : ℕ)
    (hcount : L.card = 4*m) (hlook : ∀ v ∈ L, G.deg v = k)
    (horient : ∀ e, (G.endpoints e).2 ∉ L)
    (hedge : 2*G.nE ≤ S) (hcore : ∀ v ∉ L, G.deg v ≤ D) (hD : 2 ≤ D) :
    ∃ s : LookupSeparatorSpec G.subdivision m k S D,
      s.lookupVerts = L.image G.oldVertex ∧ s.termSubdivVerts =
        (Finset.univ.filter fun e : Fin G.nE => (G.endpoints e).1 ∈ L).image G.equalityVertex := by
  classical
  let A := Finset.univ.filter fun e : Fin G.nE => (G.endpoints e).1 ∈ L
  let L' := L.image G.oldVertex
  let T' := A.image G.equalityVertex
  have hi : Function.Injective G.oldVertex := fun _ _ eq => (G.oldVertex_inj _ _).1 eq
  have hj : Function.Injective G.equalityVertex := fun _ _ eq => (G.equalityVertex_inj _ _).1 eq
  have hL (v : Fin G.nV) : G.oldVertex v ∈ L' ↔ v ∈ L := by
    constructor
    · rintro hv; rcases Finset.mem_image.mp hv with ⟨u,hu,eq⟩; exact hi eq ▸ hu
    · exact Finset.mem_image_of_mem G.oldVertex
  have hE (e : Fin G.nE) : G.equalityVertex e ∈ T' ↔ (G.endpoints e).1 ∈ L := by
    constructor
    · rintro he; change G.equalityVertex e ∈ A.image G.equalityVertex at he
      rcases Finset.mem_image.mp he with ⟨i,hi',eq⟩; exact hj eq ▸ (Finset.mem_filter.mp hi').2
    · intro he; exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,he⟩)
  have heL (e : Fin G.nE) : G.equalityVertex e ∉ L' := by
    rintro hx; rcases Finset.mem_image.mp hx with ⟨v,_,eq⟩; exact (G.oldVertex_ne_equalityVertex v e) eq
  have hA : A.card = 4*m*k := by
    have hports (v : Fin G.nV) (hv : v ∈ L) : (Finset.univ.filter fun e : Fin G.nE => (G.endpoints e).1 = v) = (G.ports v).toFinset := by
      ext e
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,List.mem_toFinset,G.mem_ports]
      have hd : (G.endpoints e).2 ≠ v := fun h => horient e (h ▸ hv)
      simp [hd]
    calc A.card = ∑ v ∈ L, (Finset.univ.filter fun e : Fin G.nE => (G.endpoints e).1 = v).card :=
                      (Finset.sum_card_fiberwise_eq_card_filter Finset.univ L _).symm
         _ = ∑ _v ∈ L, k := Finset.sum_congr rfl fun v hv => by
                rw [hports v hv,List.toFinset_card_of_nodup (G.ports_nodup v)]; exact hlook v hv
         _ = 4*m*k := by simp [hcount]
  have one_edge (e : Fin G.nE) (he : (G.endpoints e).1 ∈ L) :
      (Finset.univ.filter fun f : Fin G.subdivision.nE =>
        ((G.subdivision.endpoints f).1 = G.equalityVertex e ∧ (G.subdivision.endpoints f).2 ∈ L') ∨
        ((G.subdivision.endpoints f).2 = G.equalityVertex e ∧ (G.subdivision.endpoints f).1 ∈ L'))
        = {G.leftHalf e} := by
    ext f
    rw [Finset.mem_filter,Finset.mem_singleton]; simp only [Finset.mem_univ,true_and]
    let valid := fun f : Fin G.subdivision.nE =>
      ((G.subdivision.endpoints f).1 = G.equalityVertex e ∧ (G.subdivision.endpoints f).2 ∈ L') ∨
      ((G.subdivision.endpoints f).2 = G.equalityVertex e ∧ (G.subdivision.endpoints f).1 ∈ L')
    change valid f ↔ f = G.leftHalf e
    refine Fin.addCases (motive := fun f => valid f ↔ f = G.leftHalf e) (fun j => ?_) (fun j => ?_) f
    · change valid (G.leftHalf j) ↔ G.leftHalf j = G.leftHalf e
      unfold valid; rw [G.endpoints_leftHalf]
      constructor
      · rintro (⟨eq,_⟩ | ⟨eq,_⟩)
        · exact (G.oldVertex_ne_equalityVertex _ _ eq).elim
        · exact congrArg G.leftHalf (hj eq)
      · intro h; have heq := (G.leftHalf_inj j e).1 h; subst j; exact Or.inr ⟨rfl,(hL _).2 he⟩
    · change valid (G.rightHalf j) ↔ G.rightHalf j = G.leftHalf e
      unfold valid; rw [G.endpoints_rightHalf]
      constructor
      · rintro (⟨eq,_⟩ | ⟨_,hh⟩)
        · exact (G.oldVertex_ne_equalityVertex _ _ eq).elim
        · exact (horient j ((hL _).1 hh)).elim
      · exact fun h => (G.rightHalf_ne_leftHalf j e h).elim
  let spec : LookupSeparatorSpec G.subdivision m k S D := {
    lookupVerts := L', termSubdivVerts := T',
    disjoint_verts := by
      apply Finset.disjoint_left.mpr
      intro v hl ht; obtain ⟨e,_,rfl⟩ := Finset.mem_image.mp ht; exact heL e hl
    card_lookup := (Finset.card_image_of_injective _ hi).trans hcount
    card_termSubdiv := (Finset.card_image_of_injective _ hj).trans hA
    lookup_deg := by
      intro u hu; change u ∈ L.image G.oldVertex at hu
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hu
      rw [G.subdivision_deg_oldVertex]; exact hlook v hv
    subdiv_deg := by intro v hv; rcases Finset.mem_image.mp hv with ⟨e,he,rfl⟩; exact G.subdivision_deg_equalityVertex e
    lookup_edges_to_subdiv := by
      let law (f : Fin G.subdivision.nE) :=
        ((G.subdivision.endpoints f).1 ∈ L' → (G.subdivision.endpoints f).2 ∈ T') ∧
        ((G.subdivision.endpoints f).2 ∈ L' → (G.subdivision.endpoints f).1 ∈ T')
      intro f; refine Fin.addCases (motive := law) (fun e => ?_) (fun e => ?_) f
      · change law (G.leftHalf e); unfold law; rw [G.endpoints_leftHalf]
        exact ⟨fun hh => (hE _).2 ((hL _).1 hh), fun hh => (heL e hh).elim⟩
      · change law (G.rightHalf e); unfold law; rw [G.endpoints_rightHalf]
        exact ⟨fun hh => (horient e ((hL _).1 hh)).elim, fun hh => (heL e hh).elim⟩
    subdiv_one_lookup_edge := by
      intro v hv; rcases Finset.mem_image.mp hv with ⟨e,he,rfl⟩
      rw [one_edge e (Finset.mem_filter.mp he).2,Finset.card_singleton]
    core_edges_le := (Finset.card_filter_le ..).trans (by simpa [G.subdivision_nE] using hedge)
    core_deg_le := by
      intro v; refine Fin.addCases (fun i => ?_) (fun e => ?_) v
      · change G.oldVertex i ∉ L' → G.subdivision.deg (G.oldVertex i) ≤ D
        rw [hL,G.subdivision_deg_oldVertex]; exact hcore i
      · change G.equalityVertex e ∉ L' → G.subdivision.deg (G.equalityVertex e) ≤ D
        rw [G.subdivision_deg_equalityVertex]; exact fun _ => hD }
  exact ⟨spec,rfl,rfl⟩
