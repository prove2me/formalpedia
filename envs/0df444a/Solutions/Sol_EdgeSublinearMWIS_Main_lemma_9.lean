-- Prove2me | solution 1 for EdgeSublinearMWIS.Main.lemma_9
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T15:25:49.465145+00:00
-- url     : https://prove2.me/submissions/0192b7cc-7700-4b77-aa16-cb448faca221

import Definitions.Def_EdgeSublinearMWIS_Main_Paths

open scoped BigOperators
open EdgeSublinearMWIS.Main
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.DecompositionHelpers

 theorem path_support_subset_walk {T : Type} (tree : SimpleGraph T) (acyclic : tree.IsAcyclic)
    {s t : T} (p : tree.Walk s t) (hp : p.IsPath) (q : tree.Walk s t) :
    p.support ⊆ q.support := by
  classical
  let := acyclic.subsingleton_path s t
  have h : (⟨p, hp⟩ : tree.Path s t) = q.toPath := Subsingleton.elim _ _
  have he : p = q.toPath.val := congrArg Subtype.val h
  rw [he]
  exact q.support_toPath_subset_support

 theorem vertex_walk {n : ℕ} (G : SimpleGraph (Fin n)) {T : Type} (tree : SimpleGraph T)
    (bags : T → Finset (Fin n))
    (dec : RobertsonSeymour1986.GM5.IsTreeDecomposition G tree bags)
    {s t : T} {v : Fin n} (hs : v ∈ bags s) (ht : v ∈ bags t) :
    ∃ q : tree.Walk s t, ∀ z ∈ q.support, v ∈ bags z := by
  obtain ⟨q, hq⟩ := dec.1.connected.exists_isPath s t
  exact ⟨q, fun z hz => dec.2.2.2 s z t q hq hz (Finset.mem_inter.mpr ⟨hs, ht⟩)⟩

 theorem walk_bags {n : ℕ} (G : SimpleGraph (Fin n)) {T : Type} (tree : SimpleGraph T)
    (bags : T → Finset (Fin n))
    (dec : RobertsonSeymour1986.GM5.IsTreeDecomposition G tree bags)
    {u v : Fin n} (p : G.Walk u v) {s t : T} (hs : u ∈ bags s) (ht : v ∈ bags t) :
    ∃ q : tree.Walk s t, ∀ z ∈ q.support, ∃ x ∈ p.support, x ∈ bags z := by
  induction p generalizing s with
  | nil =>
    obtain ⟨q, hq⟩ := vertex_walk G tree bags dec hs ht
    exact ⟨q, fun z hz => ⟨_, by simp, hq z hz⟩⟩
  | @cons u v w hadj p ih =>
    obtain ⟨b, hu, hv⟩ := dec.2.2.1 u v hadj
    obtain ⟨q1, hq1⟩ := vertex_walk G tree bags dec hs hu
    obtain ⟨q2, hq2⟩ := ih hv ht
    refine ⟨q1.append q2, ?_⟩
    intro z hz
    rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hz with hz | hz
    · exact ⟨u, by simp, hq1 z hz⟩
    · obtain ⟨x, hx, hxz⟩ := hq2 z hz
      exact ⟨x, by simp [hx], hxz⟩

 theorem list_walk_between {n : ℕ} (G : SimpleGraph (Fin n)) (l : List (Fin n))
    (hne : l ≠ []) (chain : l.IsChain G.Adj) {u v : Fin n} (hu : u ∈ l) (hv : v ∈ l) :
    ∃ q : G.Walk u v, q.support ⊆ l := by
  classical
  let p := SimpleGraph.Walk.ofSupport l hne chain
  have hpu : u ∈ p.support := by simpa [p] using hu
  have hpv : v ∈ p.support := by simpa [p] using hv
  refine ⟨(p.takeUntil u hpu).reverse.append (p.takeUntil v hpv), ?_⟩
  intro x hx
  rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hx with hx | hx
  · have : x ∈ p.support := p.support_takeUntil_subset_support hpu (by simpa using hx)
    simpa [p] using this
  · have : x ∈ p.support := p.support_takeUntil_subset_support hpv hx
    simpa [p] using this

 noncomputable def touched {h n : ℕ} {H : SimpleGraph (Fin h)} {G : SimpleGraph (Fin n)}
    (embedding : AlmostEmbedding H G) (v : Fin n) : Finset (Fin h) := by
  classical
  exact Finset.univ.filter (fun x => ∃ e : EdgeIndex H,
    (x = e.val.1 ∨ x = e.val.2) ∧ v ∈ embedding.path e)

 theorem mem_touched {h n : ℕ} {H : SimpleGraph (Fin h)} {G : SimpleGraph (Fin n)}
    (embedding : AlmostEmbedding H G) (v : Fin n) (x : Fin h) :
    x ∈ touched embedding v ↔ ∃ e : EdgeIndex H,
      (x = e.val.1 ∨ x = e.val.2) ∧ v ∈ embedding.path e := by
  classical
  simp [touched]

 theorem endpoint_mem {h n : ℕ} {H : SimpleGraph (Fin h)} {G : SimpleGraph (Fin n)}
    (embedding : AlmostEmbedding H G) (e : EdgeIndex H) {x : Fin h}
    (hx : x = e.val.1 ∨ x = e.val.2) : embedding.vertex x ∈ embedding.path e := by
  rcases hx with rfl | rfl
  · exact List.mem_of_head? (embedding.valid e).2.1
  · exact List.mem_of_getLast? (embedding.valid e).2.2

 theorem incident_edge {h : ℕ} (H : SimpleGraph (Fin h)) {x y : Fin h} (hxy : H.Adj x y) :
    ∃ e : EdgeIndex H, (x = e.val.1 ∨ x = e.val.2) ∧ (y = e.val.1 ∨ y = e.val.2) := by
  rcases lt_or_gt_of_ne (H.ne_of_adj hxy) with h | h
  · exact ⟨⟨(x,y), h, hxy⟩, Or.inl rfl, Or.inr rfl⟩
  · exact ⟨⟨(y,x), h, hxy.symm⟩, Or.inr rfl, Or.inl rfl⟩

 theorem touched_card {h n : ℕ} (H : SimpleGraph (Fin h)) (G : SimpleGraph (Fin n))
    (embedding : AlmostEmbedding H G) (d : ℕ) (hd : ∀ v, degree H v ≤ d) (v : Fin n) :
    (touched embedding v).card ≤ 2 * d := by
  classical
  by_cases hne : (touched embedding v).Nonempty
  · obtain ⟨x, hx⟩ := hne
    obtain ⟨e, hxe, hve⟩ := (mem_touched embedding v x).mp hx
    have hsub : touched embedding v ⊆ H.neighborFinset e.val.1 ∪ H.neighborFinset e.val.2 := by
      intro y hy
      obtain ⟨f, hyf, hvf⟩ := (mem_touched embedding v y).mp hy
      have shares : e.val.1 = f.val.1 ∨ e.val.1 = f.val.2 ∨ e.val.2 = f.val.1 ∨ e.val.2 = f.val.2 := by
        by_contra hh
        push Not at hh
        exact embedding.disjoint e f hh.1 hh.2.1 hh.2.2.1 hh.2.2.2 v hve hvf
      have he := e.property.2
      have hes := he.symm
      have hf := f.property.2
      have hfs := hf.symm
      simp only [Finset.mem_union, SimpleGraph.mem_neighborFinset]
      rcases hyf with rfl | rfl <;> rcases shares with hh | hh | hh | hh <;> aesop
    have hdeg (u : Fin h) : (H.neighborFinset u).card ≤ d := by
      simpa only [degree, Set.ncard_eq_toFinset_card', SimpleGraph.neighborFinset_def] using hd u
    calc
      (touched embedding v).card ≤ (H.neighborFinset e.val.1 ∪ H.neighborFinset e.val.2).card := Finset.card_le_card hsub
      _ ≤ (H.neighborFinset e.val.1).card + (H.neighborFinset e.val.2).card := Finset.card_union_le _ _
      _ ≤ 2 * d := by have h1 := hdeg e.val.1; have h2 := hdeg e.val.2; omega
  · simp [Finset.not_nonempty_iff_eq_empty.mp hne]

end EdgeSublinearMWIS.Main.DecompositionHelpers


open scoped BigOperators
open EdgeSublinearMWIS.Main EdgeSublinearMWIS.Main.DecompositionHelpers
set_option autoImplicit false

theorem solution {h n : ℕ} (H : SimpleGraph (Fin h)) (G : SimpleGraph (Fin n))
    (d w : ℕ) (hdegree : ∀ v, degree H v ≤ d) (hisolated : ∀ v, ∃ u, H.Adj v u)
    (embedding : AlmostEmbedding H G) (T : Type) (tree : SimpleGraph T)
    (bags : T → Finset (Fin n))
    (decomposition : RobertsonSeymour1986.GM5.IsTreeDecomposition G tree bags)
    (size : ∀ t, (bags t).card ≤ w) :
    ∃ newBags : T → Finset (Fin h),
      RobertsonSeymour1986.GM5.IsTreeDecomposition H tree newBags ∧
        ∀ t, (newBags t).card ≤ 2 * d * w := by
  classical
  let newBags : T → Finset (Fin h) := fun t => (bags t).biUnion (touched embedding)
  have new_mem (t : T) (x : Fin h) : x ∈ newBags t ↔
      ∃ v ∈ bags t, ∃ e : EdgeIndex H, (x = e.val.1 ∨ x = e.val.2) ∧ v ∈ embedding.path e := by
    simp [newBags, mem_touched]
  refine ⟨newBags, ⟨decomposition.1, ?_, ?_, ?_⟩, ?_⟩
  · intro x
    obtain ⟨y, hxy⟩ := hisolated x
    obtain ⟨e, hxe, hye⟩ := incident_edge H hxy
    obtain ⟨t, ht⟩ := decomposition.2.1 (embedding.vertex x)
    refine ⟨t, (new_mem t x).mpr ?_⟩
    exact ⟨embedding.vertex x, ht, e, hxe, endpoint_mem embedding e hxe⟩
  · intro x y hxy
    obtain ⟨e, hxe, hye⟩ := incident_edge H hxy
    obtain ⟨t, ht⟩ := decomposition.2.1 (embedding.vertex x)
    have hmem := endpoint_mem embedding e hxe
    exact ⟨t, (new_mem t x).mpr ⟨_, ht, e, hxe, hmem⟩,
      (new_mem t y).mpr ⟨_, ht, e, hye, hmem⟩⟩
  · intro s s' s'' p hp hmid x hx
    obtain ⟨v, hv, e, hxe, hve⟩ := (new_mem s x).mp (Finset.mem_inter.mp hx).1
    obtain ⟨u, hu, f, hxf, huf⟩ := (new_mem s'' x).mp (Finset.mem_inter.mp hx).2
    obtain ⟨q1, hq1⟩ := list_walk_between G (embedding.path e)
      (embedding.valid e).1.1 (embedding.valid e).1.2.2.2 hve (endpoint_mem embedding e hxe)
    obtain ⟨q2, hq2⟩ := list_walk_between G (embedding.path f)
      (embedding.valid f).1.1 (embedding.valid f).1.2.2.2 (endpoint_mem embedding f hxf) huf
    obtain ⟨R, hR⟩ := walk_bags G tree bags decomposition (q1.append q2) hv hu
    have hmidR := path_support_subset_walk tree decomposition.1.isAcyclic p hp R hmid
    obtain ⟨z, hz, hzb⟩ := hR s' hmidR
    refine (new_mem s' x).mpr ⟨z, hzb, ?_⟩
    rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hz with hz | hz
    · exact ⟨e, hxe, hq1 hz⟩
    · exact ⟨f, hxf, hq2 hz⟩
  · intro t
    calc
      (newBags t).card ≤ ∑ v ∈ bags t, (touched embedding v).card := Finset.card_biUnion_le
      _ ≤ ∑ _v ∈ bags t, 2 * d := Finset.sum_le_sum (fun v hv => touched_card H G embedding d hdegree v)
      _ = (bags t).card * (2 * d) := by simp
      _ ≤ w * (2 * d) := Nat.mul_le_mul_right _ (size t)
      _ = 2 * d * w := Nat.mul_comm _ _
