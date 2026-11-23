-- Prove2me | solution 1 for ChenCapacityTerminals.Exact.whole_target_charges
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T07:56:18.828825+00:00
-- url     : https://prove2.me/submissions/4c933e93-6497-40f0-b6f7-c99ccfc9cd49

import Definitions.Def_ChenCapacityTerminals_Exact_GuideTargets
import Theorems.Thm_ChenCapacityTerminals_Exact_unchanged_source_capacity
set_option autoImplicit false
attribute [local instance] Classical.propDecidable
open ChenCapacityTerminals.Exact
private lemma weight_mono' {G : Network} (hG : G.Valid) {A B C D : Finset ℕ} (hAB : A ⊆ B) (hCD : C ⊆ D) : weight G A C ≤ weight G B D := by
  unfold weight
  apply List.sum_le_sum
  intro e he
  by_cases h : e.tail ∈ A ∧ e.head ∈ C
  · simp [h, hAB h.1, hCD h.2]
  · simp only [h, ↓reduceIte]
    split_ifs
    · exact (hG e he).2.2
    · exact le_rfl
private lemma mergeRound_refines (G : Network) (τ : ℝ) (P : Parts) {A : Finset ℕ} (hA : A ∈ P) : ∃ B ∈ mergeRound G τ P, A ⊆ B := by
  classical
  refine ⟨(sccParts G τ P A).biUnion id, Finset.mem_image.mpr ⟨A, hA, rfl⟩, ?_⟩
  intro x hx
  apply Finset.mem_biUnion.mpr
  refine ⟨A, ?_, hx⟩
  change A ∈ P.filter fun B => quotientReach G τ P A B ∧ quotientReach G τ P B A
  exact Finset.mem_filter.mpr ⟨hA, Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
private lemma partition_eq_of_inter {V : Finset ℕ} {P : Parts} (hP : Partition V P) {A B : Finset ℕ} (hA : A ∈ P) (hB : B ∈ P) {x : ℕ} (hxA : x ∈ A) (hxB : x ∈ B) : A = B := by
  by_contra hne
  exact (Finset.disjoint_left.mp (hP.2.2 A hA B hB hne)) hxA hxB
private lemma construction_parts_nested {G : Network} {r d : ℕ} {L : ℚ} {b : ℕ → ℕ} {t : ℕ} {c : Construction} (hc : LegalConstruction G r d L b t c)
    {i j : ℕ} (hij : i ≤ j) (hj : j ≤ c.rounds) {A B : Finset ℕ} (hA : A ∈ c.partitions i) (hB : B ∈ c.partitions j) {x : ℕ} (hxA : x ∈ A) (hxB : x ∈ B) : A ⊆ B := by
  classical
  rcases hc with ⟨hr, hp0, hpart, hmerge, hprev, hbound, hrep, hjnodup, hjspec, hjcomplete, htails, hgreedy, hfnodup, hftargets, hfinal, hpost⟩
  induction j, hij using Nat.le_induction generalizing B x with
  | base => simpa [partition_eq_of_inter (hpart i hj) hA hB hxA hxB]
  | succ j hij ih =>
      have hxV : x ∈ G.vertices := (hpart i (by omega)).1 A hA |>.2 hxA
      have hxU : x ∈ (c.partitions j).biUnion id := by rw [(hpart j (by omega)).2.1]; exact hxV
      obtain ⟨B1, hB1, hxB1⟩ := Finset.mem_biUnion.mp hxU
      have hAB1 : A ⊆ B1 := ih (by omega) hB1 hxA hxB1
      have hmergej : c.partitions (j + 1) = mergeRound G ((L : ℝ) / (4 * d)) (c.partitions j) := hmerge j (by omega)
      obtain ⟨B0, hB0, hB1B0⟩ := mergeRound_refines G ((L : ℝ) / (4 * d)) (c.partitions j) hB1
      have hB0' : B0 ∈ c.partitions (j + 1) := by rwa [hmergej]
      have heq : B0 = B := partition_eq_of_inter (hpart (j + 1) hj) hB0' hB (hB1B0 hxB1) hxB
      rw [← heq]
      exact hAB1.trans hB1B0
private lemma eq_of_nodup_map {α β : Type} {f : α → β} {l : List α} (hl : (l.map f).Nodup) {x y : α} (hx : x ∈ l) (hy : y ∈ l) (hxy : f x = f y) : x = y := by
  induction l generalizing x y with
  | nil => simp at hx
  | cons z zs ih =>
      simp only [List.map_cons, List.nodup_cons] at hl
      simp only [List.mem_cons] at hx hy
      rcases hx with rfl | hx <;> rcases hy with rfl | hy
      · rfl
      · exfalso; apply hl.1; rw [hxy]; exact List.mem_map_of_mem hy
      · exfalso; apply hl.1; rw [← hxy]; exact List.mem_map_of_mem hx
      · exact ih hl.2 hx hy hxy
private lemma nodup_of_map {α β : Type} {f : α → β} {l : List α} (hl : (l.map f).Nodup) : l.Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons x xs ih =>
      simp only [List.map_cons, List.nodup_cons] at hl
      exact List.nodup_cons.mpr ⟨fun hx => hl.1 (List.mem_map_of_mem hx), ih hl.2⟩
private def entryCharge (c : Construction) (G : Network) (e : TargetedGuideEdge) : Finset ℕ := if e.tail = dummy G then c.greedy.toFinset \ e.target else {e.tail}
private def chargesArc (c : Construction) (G : Network) (e : TargetedGuideEdge) (a : Arc) : Prop := a.tail ∈ entryCharge c G e ∧ a.head ∈ e.target
private lemma list_sum_swap {W : List TargetedGuideEdge} {arcs : List Arc} (f : TargetedGuideEdge → Arc → ℝ) :
    (W.map fun e => (arcs.map fun a => f e a).sum).sum = (arcs.map fun a => (W.map fun e => f e a).sum).sum := by
  induction W generalizing arcs with
  | nil => simp
  | cons e W ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih]
      have hadd : (arcs.map fun a => f e a + (W.map fun e' => f e' a).sum).sum = (arcs.map fun a => f e a).sum + (arcs.map fun a => (W.map fun e' => f e' a).sum).sum := by
        induction arcs with
        | nil => simp
        | cons a arcs ih' => simp only [List.map_cons, List.sum_cons, ih']; ring
      rw [← hadd]
private lemma filter_length_le_one {α : Type} {l : List α} (hl : l.Nodup) {p : α → Prop} [DecidablePred p]
    (h : ∀ x ∈ l, ∀ y ∈ l, p x → p y → x = y) : (l.filter p).length ≤ 1 := by
  classical
  have hf := hl.filter p
  cases hlf : l.filter p with
  | nil => simp
  | cons x xs =>
      have hx : x ∈ l.filter p := by rw [hlf]; simp
      have hxs : xs = [] := by
        by_contra hn
        obtain ⟨y, ys, rfl⟩ := List.exists_cons_of_ne_nil hn
        have hy : y ∈ l.filter p := by rw [hlf]; simp
        have hxp : p x := by simpa using (List.mem_filter.mp hx).2
        have hyp : p y := by simpa using (List.mem_filter.mp hy).2
        have hxy : x = y := h x (List.mem_filter.mp hx).1 y (List.mem_filter.mp hy).1 hxp hyp
        have hcons : (x :: y :: ys).Nodup := by rw [← hlf]; exact hf
        exact (List.nodup_cons.mp hcons).1 (by simp [hxy])
      simp [hxs]
private lemma list_sum_ite_charge (W : List TargetedGuideEdge) (c : Construction) (G : Network) (a : Arc) :
    (W.map fun e => if chargesArc c G e a then a.capacity else 0).sum = (W.filter fun e => chargesArc c G e a).length * a.capacity := by
  induction W with
  | nil => simp
  | cons e W ih =>
      by_cases hea : chargesArc c G e a
      · simp [hea, ih, add_comm, add_mul]
      · simp [hea, ih]
private lemma charged_weights_le_cut {G : Network} (hG : G.Valid) (c : Construction) (X : Finset ℕ) (W : List TargetedGuideEdge)
    (hW : W.Nodup) (hsub : ∀ e ∈ W, e.target ⊆ X) (houtside : ∀ e ∈ W, entryCharge c G e ⊆ G.vertices \ X)
    (hunique : ∀ a ∈ G.arcs, ∀ e ∈ W, ∀ f ∈ W, chargesArc c G e a → chargesArc c G f a → e = f) :
    (W.map fun e => weight G (entryCharge c G e) e.target).sum ≤ cut G X := by
  classical
  unfold weight cut
  rw [list_sum_swap]
  apply List.sum_le_sum
  intro a ha
  have hlen : (W.filter fun e => chargesArc c G e a).length ≤ 1 := by apply filter_length_le_one hW; intro e he f hf hea hfa; exact hunique a ha e he f hf hea hfa
  have hnonneg : 0 ≤ a.capacity := (hG a ha).2.2
  have hle : (W.map fun e => if chargesArc c G e a then a.capacity else 0).sum ≤ a.capacity := by
    rw [list_sum_ite_charge]
    have hreal : ((W.filter fun e => chargesArc c G e a).length : ℝ) ≤ 1 := by exact_mod_cast hlen
    nlinarith
  have hcross : (W.map fun e => if chargesArc c G e a then a.capacity else 0).sum = 0 ∨ (a.tail ∈ G.vertices \ X ∧ a.head ∈ X) := by
    by_cases hex : ∃ e ∈ W, chargesArc c G e a
    · obtain ⟨e, he, hea⟩ := hex
      exact Or.inr ⟨houtside e he hea.1, hsub e he hea.2⟩
    · left
      push_neg at hex
      apply List.sum_eq_zero
      intro z hz
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hz
      simp [hex e he]
  have H : (W.map fun e => if chargesArc c G e a then a.capacity else 0).sum ≤ if a.tail ∈ G.vertices \ X ∧ a.head ∈ X then a.capacity else 0 := by
    rcases hcross with hz | hcross
    · rw [hz]; split_ifs; exact hnonneg; exact le_rfl
    · simpa [hcross] using hle
  have heq : (W.map fun e => if a.tail ∈ entryCharge c G e ∧ a.head ∈ e.target then a.capacity else 0) = (W.map fun e => if chargesArc c G e a then a.capacity else 0) := by
    apply List.map_congr_left
    intro e he
    by_cases h : a.tail ∈ entryCharge c G e ∧ a.head ∈ e.target
    · have hc : chargesArc c G e a := h
      simp [h, hc]
    · have hc : ¬chargesArc c G e a := by simpa [chargesArc] using h
      simp [h, hc]
  rw [heq]
  exact H
private lemma join_edge_child {G : Network} {L : ℚ} {d : ℕ} {c : Construction} {j : JoinGuide} {p : ℕ × Finset ℕ}
    (hp : p ∈ j.edges) (hlegal : LegalJoin G ((L : ℝ) / (4 * d)) c.representative j) : p.2 ∈ j.children := by
  have hm : p.2 ∈ j.edges.map Prod.snd := List.mem_map_of_mem hp
  rw [← List.mem_toFinset, hlegal.2.2.2.2.2.2.1] at hm
  exact (Finset.mem_sdiff.mp hm).1
private lemma join_edge_data {G : Network} {r d : ℕ} {L : ℚ} {b : ℕ → ℕ} {t : ℕ} {c : Construction}
    (hc : LegalConstruction G r d L b t c) {j : JoinGuide} (hj : j ∈ c.joins) {p : ℕ × Finset ℕ} (hp : p ∈ j.edges) :
    ∃ i < c.rounds, j.parent ∈ c.partitions (i + 1) ∧ j.parent ∉ c.partitions i ∧ j.children = (c.partitions i).filter (fun C => C ⊆ j.parent) ∧
      p.2 ∈ j.children ∧ p.1 ∈ j.parent ∧ p.1 ∈ G.vertices ∧ ∃ A ∈ j.children, p.1 ∈ A ∧ A ≠ p.2 := by
  obtain ⟨hlegal, i, hi, hjp, hjnew, hjchildren⟩ := (hc.2.2.2.2.2.2.2.2.1 j hj)
  rcases hlegal with ⟨hcard, hP, hheavy, hcards, hrepr, hnodup, htargets, hwit, hreach⟩
  have hchild : p.2 ∈ j.children := by
    have hm : p.2 ∈ j.edges.map Prod.snd := List.mem_map_of_mem hp
    rw [← List.mem_toFinset, htargets] at hm
    exact (Finset.mem_sdiff.mp hm).1
  obtain ⟨A, hA, hpA, hane, hw⟩ := hwit p.1 p.2 hp
  have hpParent : p.1 ∈ j.parent := (hP.1 A hA).2 hpA
  have hpV : p.1 ∈ G.vertices := (hc.2.2.1 (i + 1) (by omega)).1 j.parent hjp |>.2 hpParent
  exact ⟨i, hi, hjp, hjnew, hjchildren, hchild, hpParent, hpV, A, hA, hpA, hane⟩
private lemma join_target_not_later {G : Network} {r d : ℕ} {L : ℚ} {b : ℕ → ℕ} {t : ℕ} {c : Construction}
    (hc : LegalConstruction G r d L b t c) {j : JoinGuide} (hj : j ∈ c.joins) {C : Finset ℕ} (hC : C ∈ j.children)
    {i k : ℕ} (hi : i < c.rounds) (hik : i < k) (hk : k ≤ c.rounds)
    (hform : j.parent ∈ c.partitions (i + 1) ∧ j.parent ∉ c.partitions i ∧ j.children = (c.partitions i).filter fun C => C ⊆ j.parent) (hCk : C ∈ c.partitions k) : False := by
  have hjspec := (hc.2.2.2.2.2.2.2.2.1 j hj).1
  rcases hjspec with ⟨hcard, hpart, hheavy, hsizes, hrep, hnodup, hset, hwit, hreach⟩
  have hCi : C ∈ c.partitions i := by have h := hC; rw [hform.2.2] at h; exact (Finset.mem_filter.mp h).1
  have hCparent : C ⊆ j.parent := (hpart.1 C hC).2
  obtain ⟨x, hxC⟩ := (hpart.1 C hC).1
  have hparentC : j.parent ⊆ C := construction_parts_nested hc (by omega) hk hform.1 hCk (hCparent hxC) hxC
  have heq : j.parent = C := Finset.Subset.antisymm hparentC hCparent
  apply hform.2.1
  rw [heq]
  exact hCi
private lemma join_target_unique {G : Network} {r d : ℕ} {L : ℚ} {b : ℕ → ℕ} {t : ℕ} {c : Construction}
    (hc : LegalConstruction G r d L b t c) {j k : JoinGuide} (hj : j ∈ c.joins) (hk : k ∈ c.joins) {e : ℕ × Finset ℕ}
    (he : e ∈ j.edges) {f : ℕ × Finset ℕ} (hf : f ∈ k.edges) (htarget : e.2 = f.2) : j = k ∧ e = f := by
  have hjl := (hc.2.2.2.2.2.2.2.2.1 j hj).1
  have hkl := (hc.2.2.2.2.2.2.2.2.1 k hk).1
  obtain ⟨i, hi, hjp, hjnew, hjchildren, hCe, hpParent, hpV, A, hA, hpA, hane⟩ := join_edge_data hc hj he
  obtain ⟨l, hl, hkp, hknew, hkchildren, hCf, hqParent, hqV, B, hB, hqB, hbne⟩ := join_edge_data hc hk hf
  have hil : i = l := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have hCf' : e.2 ∈ k.children := by simpa [htarget] using hCf
      have hCfpart : e.2 ∈ c.partitions l := by have hh := hCf'; rw [hkchildren] at hh; exact (Finset.mem_filter.mp hh).1
      exact join_target_not_later hc hj hCe hi h (by omega) ⟨hjp, hjnew, hjchildren⟩ hCfpart
    · have hCe' : f.2 ∈ j.children := by simpa [← htarget] using hCe
      have hCepart : f.2 ∈ c.partitions i := by have hh := hCe'; rw [hjchildren] at hh; exact (Finset.mem_filter.mp hh).1
      exact join_target_not_later hc hk hCf hl h (by omega) ⟨hkp, hknew, hkchildren⟩ hCepart
  have hjp' : j.parent ∈ c.partitions (l + 1) := by cases hil; exact hjp
  obtain ⟨x, hxC⟩ := (hjl.2.1.1 e.2 hCe).1
  have hxF : x ∈ f.2 := by simpa [← htarget] using hxC
  have hp : j.parent = k.parent := partition_eq_of_inter (hc.2.2.1 (l + 1) (by omega)) hjp' hkp ((hjl.2.1.1 e.2 hCe).2 hxC) ((hkl.2.1.1 f.2 hCf).2 hxF)
  have hjk : j = k := eq_of_nodup_map hc.2.2.2.2.2.2.2.1 hj hk hp
  have hedge : j.edges = k.edges := congrArg JoinGuide.edges hjk
  have hf' : f ∈ j.edges := by rw [hedge]; exact hf
  exact ⟨hjk, eq_of_nodup_map hjl.2.2.2.2.2.1 he hf' htarget⟩
private lemma join_final_target_absurd {G : Network} {r d : ℕ} {L : ℚ} {b : ℕ → ℕ} {t : ℕ} {c : Construction}
    (hc : LegalConstruction G r d L b t c) {j : JoinGuide} (hj : j ∈ c.joins) {C : Finset ℕ} (hC : C ∈ j.children) (hQ : C ∈ c.partitions c.rounds) : False := by
  let i : ℕ := Classical.choose (hc.2.2.2.2.2.2.2.2.1 j hj).2
  have hi : i < c.rounds := (Classical.choose_spec (hc.2.2.2.2.2.2.2.2.1 j hj).2).1
  have hjp : j.parent ∈ c.partitions (i + 1) := (Classical.choose_spec (hc.2.2.2.2.2.2.2.2.1 j hj).2).2.1
  have hjnew : j.parent ∉ c.partitions i := (Classical.choose_spec (hc.2.2.2.2.2.2.2.2.1 j hj).2).2.2.1
  have hjchildren : j.children = (c.partitions i).filter (fun C => C ⊆ j.parent) := (Classical.choose_spec (hc.2.2.2.2.2.2.2.2.1 j hj).2).2.2.2
  exact join_target_not_later hc hj hC hi hi (by omega) ⟨hjp, hjnew, hjchildren⟩ hQ
private lemma targetedGuide_mem {c : Construction} {G : Network} {τ : ℝ} {e : TargetedGuideEdge} (he : e ∈ c.targetedGuide G τ) :
    (∃ j ∈ c.joins, ∃ p ∈ j.edges, e = ⟨p.1, c.representative p.2, p.2⟩) ∨ (∃ p ∈ c.finalEdges, e = ⟨p.1, c.representative p.2, p.2⟩) ∨
    (∃ C ∈ c.finalSources G τ, e = ⟨dummy G, c.representative C, C⟩) := by
  classical
  rw [Construction.targetedGuide] at he
  simp only [List.mem_append, List.mem_flatMap, List.mem_map] at he
  rcases he with (⟨j, hj, p, hp, rfl⟩ | ⟨p, hp, rfl⟩) | ⟨C, hC, rfl⟩
  · exact Or.inl ⟨j, hj, p, hp, rfl⟩
  · exact Or.inr (Or.inl ⟨p, hp, rfl⟩)
  · exact Or.inr (Or.inr ⟨C, by simpa using hC, rfl⟩)
private lemma flatMap_map_nodup {α β γ : Type} {l : List α} (hl : l.Nodup) (f : α → List β) (g : β → γ)
    (hinner : ∀ a ∈ l, ((f a).map g).Nodup) (hunique : ∀ a ∈ l, ∀ b ∈ l, ∀ x ∈ f a, ∀ y ∈ f b, g x = g y → a = b ∧ x = y) : ((l.flatMap f).map g).Nodup := by
  induction l with
  | nil => simp
  | cons a as ih =>
      simp only [List.nodup_cons] at hl
      simp only [List.flatMap_cons, List.map_append]
      apply List.Nodup.append
      · exact hinner a (by simp)
      · apply ih hl.2
        · intro z hz; exact hinner z (by simp [hz])
        · intro z hz w hw x hx y hy; exact hunique z (by simp [hz]) w (by simp [hw]) x hx y hy
      · intro z hz1 hz2
        simp only [List.mem_map] at hz1 hz2
        obtain ⟨x, hx, hxz⟩ := hz1
        obtain ⟨y, hy, hyz⟩ := hz2
        obtain ⟨b, hb, hyb⟩ := List.mem_flatMap.mp hy
        have hh := hunique a (by simp) b (by simp [hb]) x hx y hyb (hxz.trans hyz.symm)
        have hna : a ≠ b := by intro hab; subst b; exact hl.1 hb
        exact hna hh.1
private lemma targetedGuide_target_nodup {G : Network} {r d : ℕ} {L : ℚ} {b : ℕ → ℕ} {t : ℕ} {c : Construction} (hc : LegalConstruction G r d L b t c) :
    ((c.targetedGuide G ((L : ℝ) / (4 * d))).map TargetedGuideEdge.target).Nodup := by
  classical
  have hc0 := hc
  rcases hc with ⟨hr, hp0, hpart, hmerge, hprev, hbound, hrep, hjnodup, hjspec, hjcomplete, htails, hgreedy, hfnodup, hftargets, hfinal, hpost⟩
  let τ : ℝ := (L : ℝ) / (4 * d)
  let jf : JoinGuide → List TargetedGuideEdge := fun j => j.edges.map fun e => ⟨e.1, c.representative e.2, e.2⟩
  let ff : List TargetedGuideEdge := c.finalEdges.map fun e => ⟨e.1, c.representative e.2, e.2⟩
  let df : List TargetedGuideEdge := (c.finalSources G τ).toList.map fun C => ⟨dummy G, c.representative C, C⟩
  have hjoins : c.joins.Nodup := nodup_of_map hjnodup
  have hj : ((c.joins.flatMap jf).map TargetedGuideEdge.target).Nodup := by
    refine flatMap_map_nodup (f := jf) (g := TargetedGuideEdge.target) hjoins ?_ ?_
    · intro j hj
      simpa only [jf, List.map_map, Function.comp_def] using (hjspec j hj).1.2.2.2.2.2.1
    · intro j hj k hk x hx y hy hxy
      simp only [jf, List.mem_map] at hx hy
      obtain ⟨e, he, rfl⟩ := hx
      obtain ⟨f, hf, rfl⟩ := hy
      have hxy' : e.2 = f.2 := hxy
      have hh := join_target_unique hc0 hj hk he hf hxy'
      exact ⟨hh.1, congrArg (fun z : ℕ × Finset ℕ => (⟨z.1, c.representative z.2, z.2⟩ : TargetedGuideEdge)) hh.2⟩
  have hf : (ff.map TargetedGuideEdge.target).Nodup := by simpa only [ff, List.map_map, Function.comp_def] using hfnodup
  have hd : (df.map TargetedGuideEdge.target).Nodup := by
    dsimp [df]
    rw [List.map_map]
    change (List.map (fun C : Finset ℕ => C) (c.finalSources G τ).toList).Nodup
    exact List.Nodup.map (fun _ _ h => h) (Finset.nodup_toList (c.finalSources G τ))
  have hlistjd : ∀ C ∈ (c.joins.flatMap jf).map TargetedGuideEdge.target, C ∉ ff.map TargetedGuideEdge.target := by
    intro C hCj hCf
    simp only [List.mem_map, List.mem_flatMap] at hCj
    simp only [ff, List.map_map, List.mem_map, Function.comp_def] at hCf
    obtain ⟨e, he, hCe⟩ := hCj
    obtain ⟨j, hj, he⟩ := he
    change e ∈ j.edges.map (fun p : ℕ × Finset ℕ => (⟨p.1, c.representative p.2, p.2⟩ : TargetedGuideEdge)) at he
    obtain ⟨p, hp, hep⟩ := List.mem_map.mp he
    obtain ⟨q, hq, hqf⟩ := hCf
    have hpC : p.2 = C := (congrArg TargetedGuideEdge.target hep).trans hCe
    have hCchild : C ∈ j.children := by rw [← hpC]; exact join_edge_child hp (hjspec j hj).1
    have hQ : C ∈ c.partitions c.rounds := by
      have hqmem : q.2 ∈ c.finalEdges.map Prod.snd := List.mem_map_of_mem hq
      rw [← List.mem_toFinset, hftargets] at hqmem
      have hround := (Finset.mem_sdiff.mp hqmem).1
      rwa [hqf] at hround
    exact join_final_target_absurd hc0 hj hCchild hQ
  have hdj : ∀ C ∈ df.map TargetedGuideEdge.target, C ∉ (c.joins.flatMap jf).map TargetedGuideEdge.target := by
    intro C hCd hCj
    simp only [df, List.map_map, List.mem_map, Function.comp_def] at hCd
    obtain ⟨Q, hQ, hCQ⟩ := hCd
    have hQS : Q ∈ c.finalSources G τ := by simpa using hQ
    simp only [List.mem_map, List.mem_flatMap] at hCj
    obtain ⟨e, he, hCe⟩ := hCj
    obtain ⟨j, hj, he⟩ := he
    change e ∈ j.edges.map (fun p : ℕ × Finset ℕ => (⟨p.1, c.representative p.2, p.2⟩ : TargetedGuideEdge)) at he
    obtain ⟨p, hp, hep⟩ := List.mem_map.mp he
    have hpC : p.2 = C := (congrArg TargetedGuideEdge.target hep).trans hCe
    have hCchild : C ∈ j.children := by rw [← hpC]; exact join_edge_child hp (hjspec j hj).1
    have hQround : C ∈ c.partitions c.rounds := by rw [← hCQ]; exact (Finset.mem_filter.mp hQS).1
    exact join_final_target_absurd hc0 hj hCchild hQround
  have hdf : ∀ C ∈ df.map TargetedGuideEdge.target, C ∉ ff.map TargetedGuideEdge.target := by
    intro C hCd hCf
    simp only [df, List.map_map, List.mem_map, Function.comp_def] at hCd
    obtain ⟨Q, hQ, hCQ⟩ := hCd
    have hQS : Q ∈ c.finalSources G τ := by simpa using hQ
    simp only [ff, List.map_map, List.mem_map, Function.comp_def] at hCf
    obtain ⟨q, hq, hCq⟩ := hCf
    have hqnon : q.2 ∉ c.finalSources G τ := by
      have hm : q.2 ∈ c.finalEdges.map Prod.snd := List.mem_map_of_mem hq
      rw [← List.mem_toFinset, hftargets] at hm
      exact (Finset.mem_sdiff.mp hm).2
    apply hqnon
    have hEq : Q = q.2 := hCQ.trans hCq.symm
    rwa [← hEq]
  have hdisjJF : List.Disjoint ((c.joins.flatMap jf).map TargetedGuideEdge.target) (ff.map TargetedGuideEdge.target) := by rw [List.disjoint_left]; exact hlistjd
  have hdisjD : List.Disjoint (((c.joins.flatMap jf).map TargetedGuideEdge.target) ++ ff.map TargetedGuideEdge.target) (df.map TargetedGuideEdge.target) := by
    rw [List.disjoint_left]
    intro C hC hCd
    simp only [List.mem_append] at hC
    exact hC.elim (hdj C hCd) (hdf C hCd)
  change (((c.joins.flatMap jf) ++ ff ++ df).map TargetedGuideEdge.target).Nodup
  simp only [List.map_append]
  exact List.Nodup.append (List.Nodup.append hj hf hdisjJF) hd hdisjD
private lemma dummy_not_mem (G : Network) : dummy G ∉ G.vertices := by
  classical
  intro h
  have hs := Finset.le_sup (f := id) h
  simp only [id_eq] at hs
  unfold dummy at hs
  omega
private lemma greedy_mem_vertices {V : Finset ℕ} {groups : List (Finset ℕ)} {D : List ℕ} (hD : Greedy V groups D) : D.toFinset ⊆ V := by
  induction D generalizing groups with
  | nil => simp
  | cons v rest ih =>
      simp only [Greedy] at hD
      intro u hu
      simp only [List.mem_toFinset, List.mem_cons] at hu
      rcases hu with rfl | hu
      · exact hD.1
      · exact ih hD.2.2.2 (by simpa using hu)
private lemma final_edge_data {G : Network} {r d : ℕ} {L : ℚ} {b : ℕ → ℕ} {t : ℕ} {c : Construction}
    (hc : LegalConstruction G r d L b t c) {p : ℕ × Finset ℕ} (hp : p ∈ c.finalEdges) :
    p.2 ∈ c.partitions c.rounds ∧ p.2 ∉ c.finalSources G ((L : ℝ) / (4 * d)) ∧ p.1 ∈ G.vertices ∧
      ∃ A ∈ c.partitions (c.rounds - 1), p.1 ∈ A ∧ Disjoint A p.2 := by
  have hc0 := hc
  rcases hc0 with ⟨hr, hp0, hpart, hmerge, hprev, hbound, hrep, hjnodup, hjspec, hjcomplete, htails, hgreedy, hfnodup, hftargets, hfinalWit, hpost⟩
  have hm : p.2 ∈ c.finalEdges.map Prod.snd := List.mem_map_of_mem hp
  rw [← List.mem_toFinset, hftargets] at hm
  have ht := Finset.mem_sdiff.mp hm
  obtain ⟨A, hA, C, hC, hpA, hdisj, hCQ, hw⟩ := hfinalWit p.1 p.2 hp
  have hpV : p.1 ∈ G.vertices := (hpart (c.rounds - 1) (by omega)).1 A hA |>.2 hpA
  exact ⟨ht.1, ht.2, hpV, A, hA, hpA, hdisj⟩
private lemma join_parent_subset_later {G : Network} {r d : ℕ} {L : ℚ} {b : ℕ → ℕ} {t : ℕ} {c : Construction}
    (hc : LegalConstruction G r d L b t c) {j : JoinGuide} (hj : j ∈ c.joins) {p : ℕ × Finset ℕ} (hp : p ∈ j.edges)
    {i k : ℕ} {Q : Finset ℕ} {v : ℕ} (hi : i < c.rounds) (hik : i < k) (hk : k ≤ c.rounds)
    (hjp : j.parent ∈ c.partitions (i + 1)) (hpchild : p.2 ∈ j.children) (hQ : Q ∈ c.partitions k) (hvp : v ∈ p.2) (hvQ : v ∈ Q) : j.parent ⊆ Q := by
  have hP := (hc.2.2.2.2.2.2.2.2.1 j hj).1.2.1
  exact construction_parts_nested hc (by omega) hk hjp hQ ((hP.1 p.2 hpchild).2 hvp) hvQ
private lemma charged_entry_unique {G : Network} {r d : ℕ} {L : ℚ} {b : ℕ → ℕ} {t : ℕ} {c : Construction}
    (hc : LegalConstruction G r d L b t c) (a : Arc) {e f : TargetedGuideEdge} (he : e ∈ c.targetedGuide G ((L : ℝ) / (4 * d)))
    (hf : f ∈ c.targetedGuide G ((L : ℝ) / (4 * d))) (hea : chargesArc c G e a) (hfa : chargesArc c G f a) : e = f := by
  apply eq_of_nodup_map (targetedGuide_target_nodup hc) he hf
  rcases targetedGuide_mem he with ⟨j, hj, p, hp, rfl⟩ | ⟨p, hp, rfl⟩ | ⟨C, hC, rfl⟩ <;> rcases targetedGuide_mem hf with ⟨k, hk, q, hq, rfl⟩ | ⟨q, hq, rfl⟩ | ⟨Q, hQ, rfl⟩
  · obtain ⟨i, hi, hjp, hjnew, hjchildren, hpchild, hpParent, hpV, A, hA, hpA, hane⟩ := join_edge_data hc hj hp
    obtain ⟨l, hl, hkp, hknew, hkchildren, hqchild, hqParent, hqV, B, hB, hqB, hbne⟩ := join_edge_data hc hk hq
    have hnep : p.1 ≠ dummy G := fun h => dummy_not_mem G (h ▸ hpV)
    have hneq : q.1 ≠ dummy G := fun h => dummy_not_mem G (h ▸ hqV)
    have htailp : a.tail = p.1 := by simpa [chargesArc, entryCharge, hnep] using hea.1
    have htailq : a.tail = q.1 := by simpa [chargesArc, entryCharge, hneq] using hfa.1
    by_cases hil : i = l
    · have hjp' : j.parent ∈ c.partitions (l + 1) := by cases hil; exact hjp
      have hpP := ((hc.2.2.2.2.2.2.2.2.1 j hj).1.2.1.1 p.2 hpchild).2
      have hqP := ((hc.2.2.2.2.2.2.2.2.1 k hk).1.2.1.1 q.2 hqchild).2
      have hparent : j.parent = k.parent := partition_eq_of_inter (hc.2.2.1 (l + 1) (by omega)) hjp' hkp (hpP hea.2) (hqP hfa.2)
      have hjk : j = k := eq_of_nodup_map hc.2.2.2.2.2.2.2.1 hj hk hparent
      have hchildren : j.children = k.children := congrArg JoinGuide.children hjk
      have hqchild' : q.2 ∈ j.children := by rw [hchildren]; exact hqchild
      exact partition_eq_of_inter ((hc.2.2.2.2.2.2.2.2.1 j hj).1.2.1) hpchild hqchild' hea.2 hfa.2
    · exfalso
      rcases Nat.lt_or_gt_of_ne hil with hilt | hilt
      · have hqpart : q.2 ∈ c.partitions l := by have hh := hqchild; rw [hkchildren] at hh; exact (Finset.mem_filter.mp hh).1
        have hparentQ := join_parent_subset_later hc hj hp hi hilt (by omega) hjp hpchild hqpart hea.2 hfa.2
        have ht : q.1 = p.1 := htailq.symm.trans htailp
        have hqQ : q.1 ∈ q.2 := by rw [ht]; exact hparentQ hpParent
        exact (Finset.disjoint_left.mp ((hc.2.2.2.2.2.2.2.2.1 k hk).1.2.1.2.2 B hB q.2 hqchild hbne)) hqB hqQ
      · have hppart : p.2 ∈ c.partitions i := by have hh := hpchild; rw [hjchildren] at hh; exact (Finset.mem_filter.mp hh).1
        have hparentP := join_parent_subset_later hc hk hq hl hilt (by omega) hkp hqchild hppart hfa.2 hea.2
        have ht : p.1 = q.1 := htailp.symm.trans htailq
        have hpP : p.1 ∈ p.2 := by rw [ht]; exact hparentP hqParent
        exact (Finset.disjoint_left.mp ((hc.2.2.2.2.2.2.2.2.1 j hj).1.2.1.2.2 A hA p.2 hpchild hane)) hpA hpP
  · obtain ⟨i, hi, hjp, hjnew, hjchildren, hpchild, hpParent, hpV, A, hA, hpA, hane⟩ := join_edge_data hc hj hp
    obtain ⟨hqRound, hqnon, hqV, B, hB, hqB, hdisj⟩ := final_edge_data hc hq
    have hnep : p.1 ≠ dummy G := fun h => dummy_not_mem G (h ▸ hpV)
    have hneq : q.1 ≠ dummy G := fun h => dummy_not_mem G (h ▸ hqV)
    have htailp : a.tail = p.1 := by simpa [chargesArc, entryCharge, hnep] using hea.1
    have htailq : a.tail = q.1 := by simpa [chargesArc, entryCharge, hneq] using hfa.1
    have hparentQ := join_parent_subset_later hc hj hp hi hi (by omega) hjp hpchild hqRound hea.2 hfa.2
    have ht : q.1 = p.1 := htailq.symm.trans htailp
    have hqQ : q.1 ∈ q.2 := by rw [ht]; exact hparentQ hpParent
    exact (Finset.disjoint_left.mp hdisj hqB hqQ).elim
  · obtain ⟨i, hi, hjp, hjnew, hjchildren, hpchild, hpParent, hpV, A, hA, hpA, hane⟩ := join_edge_data hc hj hp
    have hnep : p.1 ≠ dummy G := fun h => dummy_not_mem G (h ▸ hpV)
    have htailp : a.tail = p.1 := by simpa [chargesArc, entryCharge, hnep] using hea.1
    have htailD : a.tail ∈ c.greedy.toFinset \ Q := by simpa [chargesArc, entryCharge] using hfa.1
    have hparentQ := join_parent_subset_later hc hj hp hi hi (by omega) hjp hpchild (Finset.mem_filter.mp hQ).1 hea.2 hfa.2
    have haQ : a.tail ∈ Q := by rw [htailp]; exact hparentQ hpParent
    exact ((Finset.mem_sdiff.mp htailD).2 haQ).elim
  · obtain ⟨i, hi, hkp, hknew, hkchildren, hqchild, hqParent, hqV, B, hB, hqB, hbne⟩ := join_edge_data hc hk hq
    obtain ⟨hpRound, hpnon, hpV, A, hA, hpA, hdisj⟩ := final_edge_data hc hp
    have hnep : p.1 ≠ dummy G := fun h => dummy_not_mem G (h ▸ hpV)
    have hneq : q.1 ≠ dummy G := fun h => dummy_not_mem G (h ▸ hqV)
    have htailp : a.tail = p.1 := by simpa [chargesArc, entryCharge, hnep] using hea.1
    have htailq : a.tail = q.1 := by simpa [chargesArc, entryCharge, hneq] using hfa.1
    have hparentP := join_parent_subset_later hc hk hq hi hi (by omega) hkp hqchild hpRound hfa.2 hea.2
    have ht : p.1 = q.1 := htailp.symm.trans htailq
    have hpP : p.1 ∈ p.2 := by rw [ht]; exact hparentP hqParent
    exact (Finset.disjoint_left.mp hdisj hpA hpP).elim
  · exact partition_eq_of_inter (hc.2.2.1 c.rounds (by omega)) (final_edge_data hc hp).1 (final_edge_data hc hq).1 hea.2 hfa.2
  · have htarget : p.2 = Q := partition_eq_of_inter (hc.2.2.1 c.rounds (by omega)) (final_edge_data hc hp).1 (Finset.mem_filter.mp hQ).1 hea.2 hfa.2
    exact ((final_edge_data hc hp).2.1 (htarget ▸ hQ)).elim
  · obtain ⟨i, hi, hkp, hknew, hkchildren, hqchild, hqParent, hqV, B, hB, hqB, hbne⟩ := join_edge_data hc hk hq
    have hneq : q.1 ≠ dummy G := fun h => dummy_not_mem G (h ▸ hqV)
    have htailq : a.tail = q.1 := by simpa [chargesArc, entryCharge, hneq] using hfa.1
    have htailD : a.tail ∈ c.greedy.toFinset \ C := by simpa [chargesArc, entryCharge] using hea.1
    have hparentC := join_parent_subset_later hc hk hq hi hi (by omega) hkp hqchild (Finset.mem_filter.mp hC).1 hfa.2 hea.2
    have haC : a.tail ∈ C := by rw [htailq]; exact hparentC hqParent
    exact ((Finset.mem_sdiff.mp htailD).2 haC).elim
  · have htarget : C = q.2 := partition_eq_of_inter (hc.2.2.1 c.rounds (by omega)) (Finset.mem_filter.mp hC).1 (final_edge_data hc hq).1 hea.2 hfa.2
    exact ((final_edge_data hc hq).2.1 (htarget ▸ hC)).elim
  · exact partition_eq_of_inter (hc.2.2.1 c.rounds (by omega)) (Finset.mem_filter.mp hC).1 (Finset.mem_filter.mp hQ).1 hea.2 hfa.2
private lemma whole_entry_charge {G : Network} {r d : ℕ} {L : ℚ} {b : ℕ → ℕ} {t : ℕ} {c : Construction} {X : Finset ℕ}
    (hG : Prepared G r) (hd : 1 ≤ d) (hdn : d ≤ G.vertices.card) (hL : 0 < L) (hlower : RootLowerBound G r L)
    (hc : LegalConstruction G r d L b t c) (hX : X ⊆ G.vertices \ (c.earlyProbes G r ((L : ℝ) / (4 * d)) ∪ {r}))
    {e : TargetedGuideEdge} (he : e ∈ c.targetedGuide G ((L : ℝ) / (4 * d))) (hwhole : e.target ⊆ X ∧ e.tail ∉ X) :
    (L : ℝ) / (4 * d) ≤ weight G (entryCharge c G e) e.target ∧ entryCharge c G e ⊆ G.vertices \ X := by
  have hc0 := hc
  rcases hc0 with ⟨hr, hp0, hpart, hmerge, hprev, hbound, hrepData, hjnodup, hjspec, hjcomplete, htails, hgreedyData, hfnodup, hftargets, hfinalWit, hpost⟩
  have hτ : 0 < (L : ℝ) / (4 * d) := by apply div_pos; exact_mod_cast hL; positivity
  have hgreedyOutside : c.greedy.toFinset ⊆ G.vertices \ X := by
    intro u hu
    apply Finset.mem_sdiff.mpr
    refine ⟨greedy_mem_vertices hgreedyData hu, ?_⟩
    intro huX
    have hout := (Finset.mem_sdiff.mp (hX huX)).2
    by_cases hur : u = r
    · subst u; exact hout (Finset.mem_union_right _ (Finset.mem_singleton_self r))
    · apply hout; apply Finset.mem_union_left; apply Finset.mem_union_right
      exact Finset.mem_sdiff.mpr ⟨by simpa using hu, by simpa using hur⟩
  rcases targetedGuide_mem he with ⟨j, hj, p, hp, rfl⟩ | ⟨p, hp, rfl⟩ | ⟨C, hC, rfl⟩
  · obtain ⟨i, hi, hjp, hjnew, hjchildren, hpchild, hpParent, hpV, A, hA, hpA, hane⟩ := join_edge_data hc hj hp
    have hne : p.1 ≠ dummy G := fun h => dummy_not_mem G (h ▸ hpV)
    obtain ⟨A', hA', hpA', hne', hwt⟩ := (hc.2.2.2.2.2.2.2.2.1 j hj).1.2.2.2.2.2.2.2.1 p.1 p.2 hp
    rw [show entryCharge c G ⟨p.1, c.representative p.2, p.2⟩ = {p.1} by simp [entryCharge, hne]]
    exact ⟨hwt.le, by intro u hu; rw [Finset.mem_singleton] at hu; subst u; exact Finset.mem_sdiff.mpr ⟨hpV, hwhole.2⟩⟩
  · obtain ⟨hpRound, hpnon, hpV, A, hA, hpA, hdisj⟩ := final_edge_data hc hp
    have hne : p.1 ≠ dummy G := fun h => dummy_not_mem G (h ▸ hpV)
    obtain ⟨A', hA', C', hC', hpA', hdisj', hCQ, hwt⟩ := hfinalWit p.1 p.2 hp
    rw [show entryCharge c G ⟨p.1, c.representative p.2, p.2⟩ = {p.1} by simp [entryCharge, hne]]
    exact ⟨hwt.le.trans (weight_mono' hG.1 (Finset.Subset.refl {p.1}) hCQ), by intro u hu; rw [Finset.mem_singleton] at hu; subst u; exact Finset.mem_sdiff.mpr ⟨hpV, hwhole.2⟩⟩
  · have hrepC : c.representative C ∈ C := hrepData c.rounds (by omega) C (Finset.mem_filter.mp hC).1
    have hrepX : c.representative C ∈ X := hwhole.1 hrepC
    have hrC : r ∉ C := by intro hr; exact (Finset.mem_sdiff.mp (hX (hwhole.1 hr))).2 (Finset.mem_union_right _ (Finset.mem_singleton_self r))
    have hCold : C ∈ c.partitions (c.rounds - 1) := by
      by_contra hnew
      have hCnew : C ∈ newSources G ((L : ℝ) / (4 * d)) (c.partitions (c.rounds - 1)) := Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hC).2.1, hnew, (Finset.mem_filter.mp hC).2⟩
      have hprobe : c.representative C ∈ c.earlyProbes G r ((L : ℝ) / (4 * d)) := by
        apply Finset.mem_union_left
        exact Finset.mem_image.mpr ⟨C, Finset.mem_filter.mpr ⟨hCnew, hrC⟩, rfl⟩
      exact (Finset.mem_sdiff.mp (hX hrepX)).2 (Finset.mem_union_left _ hprobe)
    have hCunchanged : C ∈ unchangedSources G r ((L : ℝ) / (4 * d)) (c.partitions (c.rounds - 1)) := Finset.mem_filter.mpr ⟨hCold, hrC, (Finset.mem_filter.mp hC).2⟩
    have hw := unchanged_source_capacity G r d L b t c hG hd hdn hL hc hlower C hCunchanged
    rw [show entryCharge c G ⟨dummy G, c.representative C, C⟩ = c.greedy.toFinset \ C by simp [entryCharge]]
    constructor
    · calc (L : ℝ) / (4 * d) ≤ 3 * ((L : ℝ) / (4 * d)) := by nlinarith
        _ = 3 * (L : ℝ) / (4 * d) := by ring
        _ ≤ weight G (c.greedy.toFinset \ C) C := hw
    · exact Finset.sdiff_subset.trans hgreedyOutside
theorem solution (G : Network) (r d : ℕ) (L : ℚ) (b : ℕ → ℕ) (t : ℕ) (c : Construction) (X : Finset ℕ)
    (hG : Prepared G r) (hd : 1 ≤ d) (hdn : d ≤ G.vertices.card) (hL : 0 < L) (hlower : RootLowerBound G r L)
    (hc : LegalConstruction G r d L b t c) (hX : X ⊆ G.vertices \ (c.earlyProbes G r ((L : ℝ) / (4 * d)) ∪ {r})) :
    (wholeTargetEntries c G ((L : ℝ) / (4 * d)) X : ℝ) ≤ cut G X / ((L : ℝ) / (4 * d)) := by
  classical
  let τ : ℝ := (L : ℝ) / (4 * d)
  let W : List TargetedGuideEdge := (c.targetedGuide G τ).filter fun e => e.tail ∉ X ∧ e.head ∈ X ∧ e.target ⊆ X
  have hτ : 0 < τ := by dsimp [τ]; apply div_pos; exact_mod_cast hL; positivity
  have hmem {e : TargetedGuideEdge} (he : e ∈ W) : e ∈ c.targetedGuide G τ ∧ e.tail ∉ X ∧ e.head ∈ X ∧ e.target ⊆ X := by have hh := List.mem_filter.mp he; exact ⟨hh.1, by simpa using hh.2⟩
  have hW : W.Nodup := (nodup_of_map (targetedGuide_target_nodup hc)).filter _
  have hcharge : ∀ e ∈ W, τ ≤ weight G (entryCharge c G e) e.target := by intro e he; have hh := hmem he; exact (whole_entry_charge hG hd hdn hL hlower hc hX hh.1 ⟨hh.2.2.2, hh.2.1⟩).1
  have houtside : ∀ e ∈ W, entryCharge c G e ⊆ G.vertices \ X := by intro e he; have hh := hmem he; exact (whole_entry_charge hG hd hdn hL hlower hc hX hh.1 ⟨hh.2.2.2, hh.2.1⟩).2
  have hunique : ∀ a ∈ G.arcs, ∀ e ∈ W, ∀ f ∈ W, chargesArc c G e a → chargesArc c G f a → e = f := by intro a ha e he f hf hea hfa; exact charged_entry_unique hc a (hmem he).1 (hmem hf).1 hea hfa
  have hcut : (W.map fun e => weight G (entryCharge c G e) e.target).sum ≤ cut G X := charged_weights_le_cut hG.1 c X W hW (fun e he => (hmem he).2.2.2) houtside hunique
  have hlowerSum : (W.map fun _ => τ).sum ≤ (W.map fun e => weight G (entryCharge c G e) e.target).sum := by apply List.sum_le_sum; exact hcharge
  have hlen : (W.length : ℝ) * τ ≤ (W.map fun e => weight G (entryCharge c G e) e.target).sum := by simpa [nsmul_eq_mul, mul_comm] using hlowerSum
  have hcount : wholeTargetEntries c G τ X = W.length := rfl
  change (wholeTargetEntries c G τ X : ℝ) ≤ cut G X / τ
  rw [hcount]
  exact (le_div_iff₀ hτ).2 (hlen.trans hcut)
