-- Prove2me | solution 1 for ConsiderChoose.StateSpace.recursion_1
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-22T19:01:02.070584+00:00
-- url     : https://prove2.me/submissions/a1abbc04-8055-4a65-b991-8ba192ff1ec9

import Mathlib
import Definitions.Def_ConsiderChoose_StateSpace_Model

namespace ConsiderChoose.StateSpace.ComponentProof

noncomputable section
open Finset SimpleGraph

lemma bip_adj_left_right {N K : ℕ} (C : Fin K → Finset (Fin N)) (i : Fin N) (j : Fin K) :
    (bip C).Adj (.inl i) (.inr j) ↔ i ∈ C j := by
  simp [bip,SimpleGraph.fromRel]

lemma bip_adj_cases {N K : ℕ} (C : Fin K → Finset (Fin N))
    {u v : Fin N ⊕ Fin K} (h : (bip C).Adj u v) :
    (∃ i j, u=.inl i ∧ v=.inr j ∧ i∈C j) ∨
    (∃ i j, v=.inl i ∧ u=.inr j ∧ i∈C j) := by
  exact h.2

abbrev graph {N K : ℕ} (C : Fin K → Finset (Fin N)) (S : Finset (Fin N))
    (T : Finset (Fin K)) := (bip C).induce (verts S T)

lemma verts_mono {N K : ℕ} {S S' : Finset (Fin N)} {T T' : Finset (Fin K)}
    (hS : S' ⊆ S) (hT : T' ⊆ T) : verts S' T' ⊆ verts S T := by
  intro v hv
  cases v with
  | inl i => exact hS hv
  | inr j => exact hT hv

lemma component_closed {N K : ℕ} {C : Fin K → Finset (Fin N)}
    {S S' : Finset (Fin N)} {T T' : Finset (Fin K)}
    (hp : IsComponent C S T S' T') {u v : verts S T}
    (hu : u.val ∈ verts S' T') (hadj : (graph C S T).Adj u v) : v.val ∈ verts S' T' := by
  change (bip C).Adj u.val v.val at hadj
  rcases bip_adj_cases C hadj with ⟨i,j,hi,hj,hc⟩ | ⟨i,j,hi,hj,hc⟩
  · have hui : i∈S' := by simpa only [verts,Set.mem_ofPred_eq,hi,Sum.elim_inl] using hu
    have hvj : j∈T := by simpa only [verts,Set.mem_ofPred_eq,hj,Sum.elim_inr] using v.property
    have hj' : j∈T' := by
      by_contra h
      exact hp.2.2.2.1 i hui j (mem_sdiff.mpr ⟨hvj,h⟩) hc
    simpa only [verts,Set.mem_ofPred_eq,hj,Sum.elim_inr] using hj'
  · have huj : j∈T' := by simpa only [verts,Set.mem_ofPred_eq,hj,Sum.elim_inr] using hu
    have hvi : i∈S := by simpa only [verts,Set.mem_ofPred_eq,hi,Sum.elim_inl] using v.property
    have hi' : i∈S' := by
      by_contra h
      exact hp.2.2.2.2 j huj i (mem_sdiff.mpr ⟨hvi,h⟩) hc
    simpa only [verts,Set.mem_ofPred_eq,hi,Sum.elim_inl] using hi'

lemma reachable_closed {V : Type*} {G : SimpleGraph V} {U : Set V}
    (hclosed : ∀ u∈U, ∀ v, G.Adj u v → v∈U) {u v : V}
    (hu : u∈U) (h : G.Reachable u v) : v∈U := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact hu
  | @cons u w v hadj p ih => exact ih (hclosed u hu w hadj)

lemma component_reachable_mem {N K : ℕ} {C : Fin K → Finset (Fin N)}
    {S S' : Finset (Fin N)} {T T' : Finset (Fin K)}
    (hp : IsComponent C S T S' T') {u v : verts S T}
    (hu : u.val ∈ verts S' T') (h : (graph C S T).Reachable u v) :
    v.val ∈ verts S' T' :=
  reachable_closed (fun _ hu _ hadj => component_closed hp hu hadj) hu h

lemma component_reachable {N K : ℕ} {C : Fin K → Finset (Fin N)}
    {S S' : Finset (Fin N)} {T T' : Finset (Fin K)}
    (hp : IsComponent C S T S' T') (u v : verts S T)
    (hu : u.val ∈ verts S' T') (hv : v.val ∈ verts S' T') :
    (graph C S T).Reachable u v := by
  let f : graph C S' T' →g graph C S T :=
    {toFun := fun w => ⟨w.val,verts_mono hp.1 hp.2.1 w.property⟩, map_rel' := fun h => h}
  have hcon : (graph C S' T').Connected := hp.2.2.1
  exact (hcon ⟨u.val,hu⟩ ⟨v.val,hv⟩).map f

lemma component_eq_of_common_vertex {N K : ℕ} {C : Fin K → Finset (Fin N)}
    {S S₁ S₂ : Finset (Fin N)} {T T₁ T₂ : Finset (Fin K)}
    (h₁ : IsComponent C S T S₁ T₁) (h₂ : IsComponent C S T S₂ T₂)
    (v : verts S T) (hv₁ : v.val ∈ verts S₁ T₁) (hv₂ : v.val ∈ verts S₂ T₂) :
    (S₁,T₁)=(S₂,T₂) := by
  have hm (u : verts S T) : u.val∈verts S₁ T₁ ↔ u.val∈verts S₂ T₂ := by
    constructor
    · intro hu
      exact component_reachable_mem h₂ hv₂ (component_reachable h₁ v u hv₁ hu)
    · intro hu
      exact component_reachable_mem h₁ hv₁ (component_reachable h₂ v u hv₂ hu)
  apply Prod.ext
  · ext i
    constructor
    · intro hi
      exact (hm ⟨.inl i,h₁.1 hi⟩).mp hi
    · intro hi
      exact (hm ⟨.inl i,h₂.1 hi⟩).mpr hi
  · ext j
    constructor
    · intro hj
      exact (hm ⟨.inr j,h₁.2.1 hj⟩).mp hj
    · intro hj
      exact (hm ⟨.inr j,h₂.2.1 hj⟩).mpr hj


def parts {N K : ℕ} {C : Fin K → Finset (Fin N)} {S : Finset (Fin N)}
    {T : Finset (Fin K)} (c : (graph C S T).ConnectedComponent) :
    Finset (Fin N) × Finset (Fin K) := by
  classical
  exact (S.filter (fun i => ∃ hi : i∈S, (⟨Sum.inl i,hi⟩ : verts S T)∈c.supp),
    T.filter (fun j => ∃ hj : j∈T, (⟨Sum.inr j,hj⟩ : verts S T)∈c.supp))

lemma parts_subset {N K : ℕ} {C : Fin K → Finset (Fin N)} {S : Finset (Fin N)}
    {T : Finset (Fin K)} (c : (graph C S T).ConnectedComponent) :
    (parts c).1 ⊆ S ∧ (parts c).2 ⊆ T := by
  classical
  exact ⟨filter_subset _ _,filter_subset _ _⟩

lemma mem_parts_iff {N K : ℕ} {C : Fin K → Finset (Fin N)} {S : Finset (Fin N)}
    {T : Finset (Fin K)} (c : (graph C S T).ConnectedComponent) (v : verts S T) :
    v.val∈verts (parts c).1 (parts c).2 ↔ v∈c.supp := by
  classical
  rcases v with ⟨v,hv⟩
  cases v with
  | inl i =>
    change (i∈S.filter _) ↔ _
    simp only [mem_filter]
    exact ⟨fun h => h.2.choose_spec,fun h => ⟨hv,⟨hv,h⟩⟩⟩
  | inr j =>
    change (j∈T.filter _) ↔ _
    simp only [mem_filter]
    exact ⟨fun h => h.2.choose_spec,fun h => ⟨hv,⟨hv,h⟩⟩⟩

lemma parts_component {N K : ℕ} {C : Fin K → Finset (Fin N)} {S : Finset (Fin N)}
    {T : Finset (Fin K)} (c : (graph C S T).ConnectedComponent) :
    IsComponent C S T (parts c).1 (parts c).2 := by
  classical
  refine ⟨(parts_subset c).1,(parts_subset c).2,?_,?_,?_⟩
  · let f : c.toSimpleGraph →g graph C (parts c).1 (parts c).2 :=
      {toFun := fun v => ⟨v.val.val,(mem_parts_iff c v.val).mpr v.property⟩,
       map_rel' := fun h => h}
    have hf : Function.Surjective f := by
      intro v
      have hv : v.val∈verts S T := verts_mono (parts_subset c).1 (parts_subset c).2 v.property
      refine ⟨⟨⟨v.val,hv⟩,(mem_parts_iff c ⟨v.val,hv⟩).mp v.property⟩,?_⟩
      rfl
    exact c.connected_toSimpleGraph.map f hf
  · intro i hi j hj hc
    let u : verts S T := ⟨.inl i,(parts_subset c).1 hi⟩
    let v : verts S T := ⟨.inr j,(mem_sdiff.mp hj).1⟩
    have hu : u∈c.supp := (mem_parts_iff c u).mp hi
    have hadj : (graph C S T).Adj u v := (bip_adj_left_right C i j).mpr hc
    have hv : v∈c.supp := (c.mem_supp_congr_adj hadj).mp hu
    exact (mem_sdiff.mp hj).2 ((mem_parts_iff c v).mpr hv)
  · intro j hj i hi hc
    let u : verts S T := ⟨.inr j,(parts_subset c).2 hj⟩
    let v : verts S T := ⟨.inl i,(mem_sdiff.mp hi).1⟩
    have hu : u∈c.supp := (mem_parts_iff c u).mp hj
    have hadj : (graph C S T).Adj v u := (bip_adj_left_right C i j).mpr hc
    have hv : v∈c.supp := (c.mem_supp_congr_adj hadj).mpr hu
    exact (mem_sdiff.mp hi).2 ((mem_parts_iff c v).mpr hv)

lemma component_exists_vertex {N K : ℕ} (C : Fin K → Finset (Fin N))
    (S : Finset (Fin N)) (T : Finset (Fin K)) (v : verts S T) :
    ∃ p∈comps C S T, v.val∈verts p.1 p.2 := by
  classical
  let c := (graph C S T).connectedComponentMk v
  refine ⟨parts c,?_,(mem_parts_iff c v).mpr rfl⟩
  exact mem_filter.mpr ⟨mem_univ _,parts_component c⟩

lemma mem_comps {N K : ℕ} {C : Fin K → Finset (Fin N)}
    {S : Finset (Fin N)} {T : Finset (Fin K)} {p : Finset (Fin N) × Finset (Fin K)} :
    p∈comps C S T ↔ IsComponent C S T p.1 p.2 := by
  classical
  simp [comps]

lemma exists_unique_type {N K : ℕ} (C : Fin K → Finset (Fin N))
    (S : Finset (Fin N)) (T : Finset (Fin K)) (j : Fin K) (hj : j∈T) :
    ∃! p : Finset (Fin N) × Finset (Fin K), p∈comps C S T ∧ j∈p.2 := by
  obtain ⟨p,hp,hj'⟩ := component_exists_vertex C S T ⟨.inr j,hj⟩
  refine ⟨p,⟨hp,hj'⟩,?_⟩
  intro q hq
  exact component_eq_of_common_vertex (mem_comps.mp hq.1) (mem_comps.mp hp) ⟨.inr j,hj⟩ hq.2 hj'

lemma exists_unique_product {N K : ℕ} (C : Fin K → Finset (Fin N))
    (S : Finset (Fin N)) (T : Finset (Fin K)) (i : Fin N) (hi : i∈S) :
    ∃! p : Finset (Fin N) × Finset (Fin K), p∈comps C S T ∧ i∈p.1 := by
  obtain ⟨p,hp,hi'⟩ := component_exists_vertex C S T ⟨.inl i,hi⟩
  refine ⟨p,⟨hp,hi'⟩,?_⟩
  intro q hq
  exact component_eq_of_common_vertex (mem_comps.mp hq.1) (mem_comps.mp hp) ⟨.inl i,hi⟩ hq.2 hi'

end
end ConsiderChoose.StateSpace.ComponentProof

namespace ConsiderChoose.StateSpace.ValueProof

noncomputable section
open Finset

abbrev revenue {N K : ℕ} (I : Instance N K) (T : Finset (Fin K)) (A : Finset (Fin N)) : ℝ :=
  ∑ j ∈ T, I.lam j * Rev I j A

lemma revenue_le_J {N K : ℕ} (I : Instance N K) (S : Finset (Fin N))
    (T : Finset (Fin K)) (A : Finset (Fin N)) (hA : A ⊆ S) : revenue I T A ≤ J I S T := by
  exact Finset.le_sup' _ (Finset.mem_powerset.mpr hA)

lemma exists_opt {N K : ℕ} (I : Instance N K) (S : Finset (Fin N)) (T : Finset (Fin K)) :
    ∃ A, A ⊆ S ∧ J I S T = revenue I T A := by
  obtain ⟨A,hA,hval⟩ := Finset.exists_mem_eq_sup' ⟨∅,Finset.empty_mem_powerset S⟩
    (fun A => revenue I T A)
  exact ⟨A,Finset.mem_powerset.mp hA,hval⟩

lemma Rev_insert_of_mem {N K : ℕ} (I : Instance N K) (S : Finset (Fin N))
    (h : S.Nonempty) (A : Finset (Fin N)) (hA : A ⊆ S) (j : Fin K)
    (hj : S.min' h ∈ I.C j) : Rev I j (insert (S.min' h) A) = I.P (S.min' h) := by
  classical
  have hn : ((insert (S.min' h) A) ∩ I.C j).Nonempty :=
    ⟨S.min' h,mem_inter.mpr ⟨mem_insert_self _ _,hj⟩⟩
  rw [Rev,dif_pos hn]
  congr 1
  apply (min'_eq_iff _ _ _).mpr
  refine ⟨mem_inter.mpr ⟨mem_insert_self _ _,hj⟩,?_⟩
  intro b hb
  obtain rfl | hb := mem_insert.mp (mem_inter.mp hb).1
  · exact le_rfl
  · exact min'_le _ _ (hA hb)

lemma Rev_insert_of_not_mem {N K : ℕ} (I : Instance N K) (i : Fin N)
    (A : Finset (Fin N)) (j : Fin K) (hj : i ∉ I.C j) :
    Rev I j (insert i A) = Rev I j A := by
  have hset : insert i A ∩ I.C j = A ∩ I.C j := by
    ext b
    simp only [mem_inter,mem_insert]
    constructor
    · rintro ⟨rfl | hb,hc⟩
      · exact (hj hc).elim
      · exact ⟨hb,hc⟩
    · exact fun hb => ⟨Or.inr hb.1,hb.2⟩
  unfold Rev
  rw [hset]

lemma revenue_insert_min {N K : ℕ} (I : Instance N K) (S : Finset (Fin N))
    (T : Finset (Fin K)) (h : S.Nonempty) (A : Finset (Fin N)) (hA : A ⊆ S) :
    revenue I T (insert (S.min' h) A) =
      I.P (S.min' h) * ∑ j ∈ typesOf I.C T (S.min' h), I.lam j +
        revenue I (T \ typesOf I.C T (S.min' h)) A := by
  classical
  have hsub : typesOf I.C T (S.min' h) ⊆ T := filter_subset _ _
  rw [revenue,← sum_sdiff hsub,add_comm]
  congr 1
  · rw [mul_sum]
    apply sum_congr rfl
    intro j hj
    rw [Rev_insert_of_mem I S h A hA j (mem_filter.mp hj).2]
    ring
  · apply sum_congr rfl
    intro j hj
    have hj' : S.min' h ∉ I.C j := by
      intro hc
      exact (mem_sdiff.mp hj).2 (mem_filter.mpr ⟨(mem_sdiff.mp hj).1,hc⟩)
    rw [Rev_insert_of_not_mem I _ A j hj']

lemma J_split {N K : ℕ} (I : Instance N K) (S : Finset (Fin N))
    (T : Finset (Fin K)) (h : S.Nonempty) :
    J I S T = max
      (I.P (S.min' h) * ∑ j ∈ typesOf I.C T (S.min' h), I.lam j +
        J I (S.erase (S.min' h)) (T \ typesOf I.C T (S.min' h)))
      (J I (S.erase (S.min' h)) T) := by
  classical
  apply le_antisymm
  · unfold J
    apply sup'_le
    intro A hA
    have hAS := mem_powerset.mp hA
    by_cases hi : S.min' h ∈ A
    · have he : A.erase (S.min' h) ⊆ S.erase (S.min' h) := erase_subset_erase _ hAS
      have hrev := revenue_insert_min I S T h (A.erase (S.min' h))
        (erase_subset _ _ |>.trans hAS)
      rw [insert_erase hi] at hrev
      change revenue I T A ≤ _
      rw [hrev]
      exact (add_le_add le_rfl (revenue_le_J I _ _ _ he)).trans (le_max_left _ _)
    · have he : A ⊆ S.erase (S.min' h) := subset_erase.mpr ⟨hAS,hi⟩
      exact (revenue_le_J I _ _ A he).trans (le_max_right _ _)
  · apply max_le
    · obtain ⟨A,hA,hopt⟩ := exists_opt I (S.erase (S.min' h)) (T \ typesOf I.C T (S.min' h))
      have hAS : A ⊆ S := hA.trans (erase_subset _ _)
      rw [hopt,← revenue_insert_min I S T h A hAS]
      exact revenue_le_J I S T _ (insert_subset (min'_mem _ _) hAS)
    · obtain ⟨A,hA,hopt⟩ := exists_opt I (S.erase (S.min' h)) T
      rw [hopt]
      exact revenue_le_J I S T A (hA.trans (erase_subset _ _))

end
end ConsiderChoose.StateSpace.ValueProof

namespace ConsiderChoose.StateSpace.ValueProof

noncomputable section
open Finset ComponentProof

lemma component_types_biUnion {N K : ℕ} (C : Fin K → Finset (Fin N))
    (S : Finset (Fin N)) (T : Finset (Fin K)) :
    (comps C S T).biUnion Prod.snd = T := by
  classical
  ext j
  constructor
  · intro hj
    obtain ⟨p,hp,hj⟩ := mem_biUnion.mp hj
    exact (mem_comps.mp hp).2.1 hj
  · intro hj
    obtain ⟨p,hp,_⟩ := exists_unique_type C S T j hj
    exact mem_biUnion.mpr ⟨p,hp.1,hp.2⟩

lemma component_types_disjoint {N K : ℕ} (C : Fin K → Finset (Fin N))
    (S : Finset (Fin N)) (T : Finset (Fin K)) :
    (comps C S T : Set (Finset (Fin N) × Finset (Fin K))).PairwiseDisjoint Prod.snd := by
  classical
  intro p hp q hq hpq
  apply disjoint_left.mpr
  intro j hjp hjq
  exact hpq (component_eq_of_common_vertex (mem_comps.mp hp) (mem_comps.mp hq)
    ⟨.inr j,(mem_comps.mp hp).2.1 hjp⟩ hjp hjq)

lemma Rev_restrict_component {N K : ℕ} (I : Instance N K) {S : Finset (Fin N)}
    {T : Finset (Fin K)} {p : Finset (Fin N) × Finset (Fin K)}
    (hp : p∈comps I.C S T) (A : Finset (Fin N)) (hA : A⊆S) (j : Fin K) (hj : j∈p.2) :
    Rev I j (A∩p.1) = Rev I j A := by
  have hcomp := mem_comps.mp hp
  have heq : (A∩p.1)∩I.C j = A∩I.C j := by
    ext i
    simp only [mem_inter]
    constructor
    · exact fun hi => ⟨hi.1.1,hi.2⟩
    · intro hi
      have hip : i∈p.1 := by
        by_contra hn
        exact hcomp.2.2.2.2 j hj i (mem_sdiff.mpr ⟨hA hi.1,hn⟩) hi.2
      exact ⟨⟨hi.1,hip⟩,hi.2⟩
  unfold Rev
  rw [heq]

lemma revenue_components {N K : ℕ} (I : Instance N K) (S : Finset (Fin N))
    (T : Finset (Fin K)) (A : Finset (Fin N)) (hA : A⊆S) :
    revenue I T A = ∑ p∈comps I.C S T, revenue I p.2 (A∩p.1) := by
  classical
  have hsum := Finset.sum_biUnion (component_types_disjoint I.C S T)
    (f := fun j => I.lam j * Rev I j A)
  rw [component_types_biUnion] at hsum
  change (∑ j∈T,I.lam j*Rev I j A) = _
  rw [hsum]
  apply sum_congr rfl
  intro p hp
  apply sum_congr rfl
  intro j hj
  rw [Rev_restrict_component I hp A hA j hj]

lemma J_components {N K : ℕ} (I : Instance N K) (S : Finset (Fin N)) (T : Finset (Fin K)) :
    J I S T = ∑ p∈comps I.C S T, J I p.1 p.2 := by
  classical
  apply le_antisymm
  · obtain ⟨A,hA,hopt⟩ := exists_opt I S T
    rw [hopt,revenue_components I S T A hA]
    apply sum_le_sum
    intro p hp
    exact revenue_le_J I p.1 p.2 (A∩p.1) inter_subset_right
  · choose a ha hopt using fun p : Finset (Fin N) × Finset (Fin K) => exists_opt I p.1 p.2
    let A := (comps I.C S T).biUnion a
    have hA : A⊆S := by
      intro i hi
      obtain ⟨p,hp,hi⟩ := mem_biUnion.mp hi
      exact (mem_comps.mp hp).1 (ha p hi)
    have hrestrict (p : Finset (Fin N) × Finset (Fin K)) (hp : p∈comps I.C S T) :
        A∩p.1=a p := by
      ext i
      constructor
      · intro hi
        obtain ⟨hiA,hip⟩ := mem_inter.mp hi
        obtain ⟨q,hq,hiq⟩ := mem_biUnion.mp hiA
        have hpq : p=q := component_eq_of_common_vertex (mem_comps.mp hp) (mem_comps.mp hq)
          ⟨.inl i,(mem_comps.mp hp).1 hip⟩ hip (ha q hiq)
        simpa only [hpq] using hiq
      · intro hi
        exact mem_inter.mpr ⟨mem_biUnion.mpr ⟨p,hp,hi⟩,ha p hi⟩
    calc
      (∑ p∈comps I.C S T,J I p.1 p.2) = ∑ p∈comps I.C S T,revenue I p.2 (A∩p.1) := by
        apply sum_congr rfl
        intro p hp
        rw [hrestrict p hp,hopt p]
      _ = revenue I T A := (revenue_components I S T A hA).symm
      _ ≤ J I S T := revenue_le_J I S T A hA

end
end ConsiderChoose.StateSpace.ValueProof

open ConsiderChoose.StateSpace ConsiderChoose.StateSpace.ValueProof

theorem solution {N K : ℕ} (I : Instance N K) (S : Finset (Fin N)) (T : Finset (Fin K))
    (h : S.Nonempty) (_hc : GConnected I.C S T) :
    J I S T =
      max (I.P (S.min' h) * ∑ j ∈ typesOf I.C T (S.min' h), I.lam j +
            ∑ p ∈ comps I.C (S.erase (S.min' h)) (T \ typesOf I.C T (S.min' h)), J I p.1 p.2)
        (∑ p ∈ comps I.C (S.erase (S.min' h)) T, J I p.1 p.2)  := by
  rw [J_split I S T h,J_components I (S.erase (S.min' h)) (T \ typesOf I.C T (S.min' h)),
    J_components I (S.erase (S.min' h)) T]
