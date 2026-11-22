-- Prove2me | solution 1 for BuchiRabinIndex.LowerBound.fact_31
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T07:34:50.241421+00:00
-- url     : https://prove2.me/submissions/ecfcf3b3-1caa-466f-bea1-0ae78a05ab24

import Definitions.Def_BuchiRabinIndex_LowerBound_Rabin
import Theorems.Thm_BuchiRabinIndex_LowerBound_fact_30

set_option autoImplicit false

namespace BuchiRabinIndex.LowerBound.Fact31Aux
open BuchiRabinIndex.LowerBound
open scoped Classical

lemma label_sub_of_prefix {Q : Type} {H : TreeData Q} (hv : Valid H) :
    ∀ (x : Node) (w : List ℕ), x ++ w ∈ H.nodes → H.label (x ++ w) ⊆ H.label x
  | x, [], _ => by simp
  | x, i :: rest, hmem => by
    have hxi_mem : x ++ [i] ∈ H.nodes :=
      hv.1.2.1 (x ++ (i :: rest)) hmem (x ++ [i]) ⟨rest, by simp⟩
    have h1 : H.label ((x ++ [i]) ++ rest) ⊆ H.label (x ++ [i]) :=
      label_sub_of_prefix hv (x ++ [i]) rest (by simpa using hmem)
    have h1' : H.label (x ++ i :: rest) ⊆ H.label (x ++ [i]) := by simpa using h1
    have hchild : x ++ [i] ∈ children H.nodes x := by
      simp [children, hxi_mem]
    have h2 : H.label (x ++ [i]) ⊆ childLabels H x :=
      Finset.subset_biUnion_of_mem H.label hchild
    have h3 : childLabels H x ⊆ H.label x :=
      (hv.2.2.2.2.2 x (hv.1.2.1 _ hxi_mem x ⟨[i], rfl⟩)).subset
    exact h1'.trans (h2.trans h3)

lemma split_incomparable :
    ∀ (x y : List ℕ), ¬ x.IsPrefix y → ¬ y.IsPrefix x →
      ∃ p i j u v, i ≠ j ∧ x = p ++ i :: u ∧ y = p ++ j :: v
  | [], _, hxy, _ => absurd List.nil_prefix hxy
  | _, [], _, hyx => absurd List.nil_prefix hyx
  | a :: xs, b :: ys, hxy, hyx => by
    by_cases hab : a = b
    · subst hab
      have hxy' : ¬ xs.IsPrefix ys := fun h => hxy (List.cons_prefix_cons.mpr ⟨rfl, h⟩)
      have hyx' : ¬ ys.IsPrefix xs := fun h => hyx (List.cons_prefix_cons.mpr ⟨rfl, h⟩)
      obtain ⟨p, i, j, u, v, hij, h1, h2⟩ := split_incomparable xs ys hxy' hyx'
      exact ⟨a :: p, i, j, u, v, hij, by simp [h1], by simp [h2]⟩
    · exact ⟨[], a, b, xs, ys, hab, rfl, rfl⟩

lemma own_disjoint {Q : Type} {H : TreeData Q} (hv : Valid H)
    {x y : Node} (hx : x ∈ H.nodes) (hy : y ∈ H.nodes) (hne : x ≠ y) :
    Disjoint (own H x) (own H y) := by
  rw [Finset.disjoint_left]
  intro q hqx hqy
  by_cases hpre1 : x.IsPrefix y
  · obtain ⟨w, rfl⟩ := hpre1
    cases w with
    | nil => exact hne (by simp)
    | cons i rest =>
      have hxi : x ++ [i] ∈ H.nodes := hv.1.2.1 _ hy (x ++ [i]) ⟨rest, by simp⟩
      have hsub : H.label ((x ++ [i]) ++ rest) ⊆ H.label (x ++ [i]) :=
        label_sub_of_prefix hv (x ++ [i]) rest (by simpa using hy)
      have hqy' : q ∈ H.label ((x ++ [i]) ++ rest) := by simpa using (Finset.mem_sdiff.mp hqy).1
      have hch : q ∈ childLabels H x :=
        Finset.mem_biUnion.mpr ⟨x ++ [i], by simp [children, hxi], hsub hqy'⟩
      exact (Finset.mem_sdiff.mp hqx).2 hch
  · by_cases hpre2 : y.IsPrefix x
    · obtain ⟨w, rfl⟩ := hpre2
      cases w with
      | nil => exact hne (by simp)
      | cons i rest =>
        have hyi : y ++ [i] ∈ H.nodes := hv.1.2.1 _ hx (y ++ [i]) ⟨rest, by simp⟩
        have hsub : H.label ((y ++ [i]) ++ rest) ⊆ H.label (y ++ [i]) :=
          label_sub_of_prefix hv (y ++ [i]) rest (by simpa using hx)
        have hqx' : q ∈ H.label ((y ++ [i]) ++ rest) := by simpa using (Finset.mem_sdiff.mp hqx).1
        have hch : q ∈ childLabels H y :=
          Finset.mem_biUnion.mpr ⟨y ++ [i], by simp [children, hyi], hsub hqx'⟩
        exact (Finset.mem_sdiff.mp hqy).2 hch
    · obtain ⟨p, i, j, u, v, hij, rfl, rfl⟩ := split_incomparable x y hpre1 hpre2
      have hpi : p ++ [i] ∈ H.nodes := hv.1.2.1 _ hx (p ++ [i]) ⟨u, by simp⟩
      have hpj : p ++ [j] ∈ H.nodes := hv.1.2.1 _ hy (p ++ [j]) ⟨v, by simp⟩
      have hqx' : q ∈ H.label ((p ++ [i]) ++ u) := by simpa using (Finset.mem_sdiff.mp hqx).1
      have hqy' : q ∈ H.label ((p ++ [j]) ++ v) := by simpa using (Finset.mem_sdiff.mp hqy).1
      have h1 : q ∈ H.label (p ++ [i]) :=
        label_sub_of_prefix hv (p ++ [i]) u (by simpa using hx) hqx'
      have h2 : q ∈ H.label (p ++ [j]) :=
        label_sub_of_prefix hv (p ++ [j]) v (by simpa using hy) hqy'
      exact Finset.disjoint_left.mp (hv.2.2.2.2.1 p i j hpi hpj hij) h1 h2

lemma nodes_card_le {Q : Type} [Fintype Q] (H : History Q) :
    H.val.nodes.card ≤ Fintype.card Q := by
  have hv := H.property
  have hdisj : (H.val.nodes : Set Node).PairwiseDisjoint (own H.val) :=
    fun x hx y hy hne => own_disjoint hv hx hy hne
  have hpos : ∀ x ∈ H.val.nodes, 1 ≤ (own H.val x).card := by
    intro x hx
    rw [Finset.one_le_card]
    have hss := hv.2.2.2.2.2 x hx
    rw [own, Finset.sdiff_nonempty]
    exact fun h => hss.not_subset h
  calc H.val.nodes.card
      = ∑ _x ∈ H.val.nodes, 1 := by simp
    _ ≤ ∑ x ∈ H.val.nodes, (own H.val x).card := Finset.sum_le_sum hpos
    _ = (H.val.nodes.biUnion (own H.val)).card := (Finset.card_biUnion hdisj).symm
    _ ≤ (Finset.univ : Finset Q).card := Finset.card_le_card (Finset.subset_univ _)
    _ = Fintype.card Q := Finset.card_univ

lemma card_chain_eq : ∀ x : Node, Positive x → (chain x).card = weight x + 1
  | [], _ => by simp [chain, weight]
  | i :: v, hx => by
    have hi : 0 < i := hx i (by simp)
    have hv : Positive v := fun k hk => hx k (by simp [hk])
    have ih := card_chain_eq v hv
    have hdisj : Disjoint ((Finset.Icc 1 (i - 1)).image fun j => [j])
        ((chain v).image (i :: ·)) := by
      rw [Finset.disjoint_left]
      intro a ha hb
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 ha
      obtain ⟨y, -, hy⟩ := Finset.mem_image.1 hb
      simp at hy hj; omega
    have hnil : [] ∉ ((Finset.Icc 1 (i - 1)).image fun j => [j]) ∪ ((chain v).image (i :: ·)) := by
      simp
    simp only [chain]
    rw [Finset.card_insert_of_notMem hnil, Finset.card_union_of_disjoint hdisj,
      Finset.card_image_of_injective _ (fun a b h => by simpa using h),
      Finset.card_image_of_injective _ (fun a b h => by simpa using h), ih]
    simp [weight]; omega

lemma mem_boundedWords (b : ℕ) : ∀ (d : ℕ) (x : Node),
    (∀ i ∈ x, 1 ≤ i ∧ i ≤ b) → x.length ≤ d → x ∈ boundedWords b d
  | 0, x, _, hl => by simp at hl; subst hl; simp [boundedWords]
  | d + 1, [], _, _ => by simp [boundedWords]
  | d + 1, a :: t, hb, hl => by
    simp only [boundedWords, Finset.mem_insert, Finset.mem_biUnion, Finset.mem_Icc, Finset.mem_image]
    right
    exact ⟨a, hb a (by simp), t,
      mem_boundedWords b d t (fun i hi => hb i (by simp [hi])) (by simp at hl; omega), rfl⟩

lemma mem_fullTree_of_pos_weight {n : ℕ} (hn : 1 ≤ n) {x : Node}
    (hx : Positive x) (hw : weight x ≤ n - 1) : x ∈ fullTree n := by
  have hn0 : n ≠ 0 := by omega
  unfold fullTree
  rw [if_neg hn0, Finset.mem_filter]
  refine ⟨?_, hw⟩
  have hsum : ∀ (l : List ℕ) (i : ℕ), i ∈ l → i ≤ l.sum := by
    intro l; induction l with
    | nil => simp
    | cons a t ih =>
      intro i hi; rcases List.mem_cons.1 hi with rfl | hi
      · simp
      · have := ih i hi; simp; omega
  have hlen : ∀ (l : List ℕ), Positive l → l.length ≤ l.sum := by
    intro l; induction l with
    | nil => simp
    | cons a t ih =>
      intro hp; have := ih (fun k hk => hp k (by simp [hk]))
      have := hp a (by simp); simp; omega
  exact mem_boundedWords (n - 1) (n - 1) x
    (fun i hi => ⟨hx i hi, (hsum x i hi).trans hw⟩) ((hlen x hx).trans hw)

lemma history_finite {Q : Type} [Fintype Q] : Finite (History Q) := by
  by_cases hQ : Fintype.card Q = 0
  · have hisEmpty : IsEmpty (History Q) := ⟨fun H => by
      have hc := nodes_card_le H
      have hne : H.val.nodes.Nonempty := ⟨[], H.property.2.1⟩
      have := Finset.card_pos.mpr hne
      omega⟩
    exact @Finite.of_fintype (History Q) (@Fintype.ofIsEmpty _ hisEmpty)
  · have hk : 1 ≤ Fintype.card Q := Nat.pos_of_ne_zero hQ
    let k := Fintype.card Q
    have hsub : ∀ H : History Q, H.val.nodes ∈ (fullTree k).powerset := by
      intro H
      rw [Finset.mem_powerset]
      intro x hx
      have hpx : Positive x := H.property.1.1 x hx
      have hch_sub : chain x ⊆ H.val.nodes :=
        (fact_30 x x hpx hpx).2.2.2.2.2.1 H.val.nodes H.property.1 hx
      have hcard : (chain x).card ≤ k :=
        (Finset.card_le_card hch_sub).trans (nodes_card_le H)
      rw [card_chain_eq x hpx] at hcard
      exact mem_fullTree_of_pos_weight hk hpx (by omega)
    let enc : History Q → ↥((fullTree k).powerset) × (Vertex k → Finset Q) :=
      fun H => (⟨H.val.nodes, hsub H⟩, fun v => H.val.label v.val)
    refine Finite.of_injective enc ?_
    intro H1 H2 heq
    have hnodes : H1.val.nodes = H2.val.nodes := congrArg (Subtype.val ∘ Prod.fst) heq
    have hlbl_on : ∀ v : Vertex k, H1.val.label v.val = H2.val.label v.val :=
      fun v => congrFun (congrArg Prod.snd heq) v
    have hlbl : H1.val.label = H2.val.label := by
      funext x
      by_cases hx : x ∈ H1.val.nodes
      · have hxf : x ∈ fullTree k := Finset.mem_powerset.mp (hsub H1) hx
        exact hlbl_on ⟨x, hxf⟩
      · have hx2 : x ∉ H2.val.nodes := hnodes ▸ hx
        rw [H1.property.2.2.1 x hx, H2.property.2.2.1 x hx2]
    apply Subtype.ext
    rcases H1 with ⟨⟨n1, l1⟩, _⟩
    rcases H2 with ⟨⟨n2, l2⟩, _⟩
    simp only at hnodes hlbl
    subst hnodes hlbl
    rfl

lemma eventually_mem_infSet {X : Type} [Finite X] (f : ℕ → X) :
    ∃ N : ℕ, ∀ i ≥ N, f i ∈ infSet f := by
  have hft : Fintype X := Fintype.ofFinite X
  have hbad : ∀ x : X, x ∉ infSet f → ∃ Nx : ℕ, ∀ i ≥ Nx, f i ≠ x := by
    intro x hx
    change ¬ (∀ N, ∃ i ≥ N, f i = x) at hx
    push_neg at hx
    exact hx
  let B : Finset X := (@Finset.univ X hft).filter (fun x => x ∉ infSet f)
  let bound : X → ℕ := fun x => if hx : x ∉ infSet f then Classical.choose (hbad x hx) else 0
  refine ⟨B.sup bound, fun i hi => ?_⟩
  by_contra hni
  have hxB : f i ∈ B := Finset.mem_filter.mpr ⟨@Finset.mem_univ X hft _, hni⟩
  have hle : bound (f i) ≤ B.sup bound := Finset.le_sup hxB
  have hspec := Classical.choose_spec (hbad (f i) hni)
  have hbound_eq : bound (f i) = Classical.choose (hbad (f i) hni) := dif_pos hni
  exact hspec i (by omega) rfl

lemma infSet_nonempty {X : Type} [Finite X] (f : ℕ → X) : (infSet f).Nonempty := by
  obtain ⟨x, hx_inf⟩ := Finite.exists_infinite_fiber f
  have hx_set : (f ⁻¹' {x}).Infinite := Set.infinite_coe_iff.mp hx_inf
  refine ⟨x, fun N => ?_⟩
  obtain ⟨i, hi_mem, hi_not_lt⟩ := (hx_set.sdiff (Set.finite_lt_nat N)).nonempty
  exact ⟨i, Nat.le_of_not_lt hi_not_lt, hi_mem⟩

lemma readWord_none {Q Sigma : Type} (B : NBW Q Sigma) :
    ∀ v : List Sigma, readWord B none v = none
  | [] => rfl
  | _ :: v => readWord_none B v

lemma readWord_append {Q Sigma : Type} (B : NBW Q Sigma) :
    ∀ (u v : List Sigma) (H : Option (History Q)),
      readWord B H (u ++ v) = readWord B (readWord B H u) v
  | [], _, _ => rfl
  | σ :: u, v, H => readWord_append B u v (H.bind fun h => successor B h σ)

lemma readWord_some_of_append {Q Sigma : Type} {B : NBW Q Sigma}
    {H : Option (History Q)} {u v : List Sigma} {K : History Q}
    (h : readWord B H (u ++ v) = some K) :
    ∃ M, readWord B H u = some M := by
  rw [readWord_append] at h
  cases hM : readWord B H u with
  | none =>
    rw [hM, readWord_none] at h
    cases h
  | some M => exact ⟨M, rfl⟩

lemma take_append_of_le {α : Type} (u v : List α) {i : ℕ} (hi : i ≤ u.length) :
    (u ++ v).take i = u.take i := by
  induction u generalizing i with
  | nil =>
    have hi0 : i = 0 := by simpa using hi
    subst hi0
    simp
  | cons a u ih =>
    cases i with
    | zero => simp
    | succ i =>
      simp only [List.cons_append, List.take_succ_cons]
      congr 1
      exact ih (by simpa using hi)

lemma take_append_add {α : Type} (u v : List α) (j : ℕ) :
    (u ++ v).take (u.length + j) = u ++ v.take j := by
  induction u with
  | nil => simp
  | cons a u ih =>
    simp only [List.length_cons, Nat.succ_add, List.cons_append, List.take_succ_cons]
    congr 1

lemma wordEdges_append {Q Sigma : Type} (B : NBW Q Sigma)
    {H : Option (History Q)} {u v : List Sigma} {K : History Q}
    (hu : readWord B H u = some K) :
    wordEdges B H (u ++ v) = wordEdges B H u ∪ wordEdges B (some K) v := by
  ext e
  simp only [wordEdges, Set.mem_union]
  change (∃ i : Fin (u ++ v).length, _) ↔ (∃ i : Fin u.length, _) ∨ (∃ i : Fin v.length, _)
  constructor
  · rintro ⟨i, hread, hlet, hsucc⟩
    simp only [Fin.getElem_fin] at hlet
    by_cases hlt : i.val < u.length
    · left
      refine ⟨⟨i.val, hlt⟩, ?_, ?_, hsucc⟩
      · rwa [take_append_of_le u v (Nat.le_of_lt hlt)] at hread
      · simp only [Fin.getElem_fin]
        rwa [List.getElem_append_left hlt] at hlet
    · right
      have hge : u.length ≤ i.val := Nat.le_of_not_lt hlt
      have hj : i.val - u.length < v.length := by
        have := i.isLt
        simp at this
        omega
      refine ⟨⟨i.val - u.length, hj⟩, ?_, ?_, hsucc⟩
      · have heq : i.val = u.length + (i.val - u.length) := by omega
        rw [heq, take_append_add, readWord_append, hu] at hread
        exact hread
      · simp only [Fin.getElem_fin]
        rwa [List.getElem_append_right hge] at hlet
  · rintro (⟨i, hread, hlet, hsucc⟩ | ⟨j, hread, hlet, hsucc⟩)
    · simp only [Fin.getElem_fin] at hlet
      have hi : i.val < (u ++ v).length := by simp; omega
      refine ⟨⟨i.val, hi⟩, ?_, ?_, hsucc⟩
      · rwa [take_append_of_le u v (Nat.le_of_lt i.isLt)]
      · simp only [Fin.getElem_fin]
        rw [List.getElem_append_left i.isLt]
        exact hlet
    · simp only [Fin.getElem_fin] at hlet
      have hj : u.length + j.val < (u ++ v).length := by simp
      refine ⟨⟨u.length + j.val, hj⟩, ?_, ?_, hsucc⟩
      · rw [take_append_add, readWord_append, hu]
        exact hread
      · simp only [Fin.getElem_fin]
        rw [List.getElem_append_right (Nat.le_add_right _ _)]
        simpa using hlet

lemma visited_append {Q Sigma : Type} (B : NBW Q Sigma)
    {H K : History Q} {u v : List Sigma}
    (hu : readWord B (some H) u = some K) :
    visited B H (u ++ v) = visited B H u ∪ visited B K v := by
  ext M
  simp only [visited, Set.mem_union, Set.mem_setOf_eq]
  constructor
  · rintro ⟨i, hi, hread⟩
    by_cases hle : i ≤ u.length
    · left
      refine ⟨i, hle, ?_⟩
      rwa [take_append_of_le u v hle] at hread
    · right
      have hj : i - u.length ≤ v.length := by simp at hi; omega
      refine ⟨i - u.length, hj, ?_⟩
      have heq : i = u.length + (i - u.length) := by omega
      rw [heq, take_append_add, readWord_append, hu] at hread
      exact hread
  · rintro (⟨i, hi, hread⟩ | ⟨j, hj, hread⟩)
    · refine ⟨i, by simp; omega, ?_⟩
      rwa [take_append_of_le u v hi]
    · refine ⟨u.length + j, by simp; omega, ?_⟩
      rw [take_append_add, readWord_append, hu]
      exact hread

lemma splice_closedWalk {Q Sigma : Type} (B : NBW Q Sigma)
    {H1 H2 M : History Q} {w1 w2 : List Sigma}
    (hw1 : ClosedWalk B H1 w1) (hw2 : ClosedWalk B H2 w2)
    (hM1 : M ∈ visited B H1 w1) (hM2 : M ∈ visited B H2 w2) :
    ∃ w : List Sigma,
      ClosedWalk B H1 w ∧
      wordEdges B (some H1) w = wordEdges B (some H1) w1 ∪ wordEdges B (some H2) w2 ∧
      visited B H1 w = visited B H1 w1 ∪ visited B H2 w2 := by
  obtain ⟨i, hi, hq1⟩ := hM1
  obtain ⟨j, hj, hp1⟩ := hM2
  let q1 := w1.take i
  let q2 := w1.drop i
  let p1 := w2.take j
  let p2 := w2.drop j
  have hw1_eq : q1 ++ q2 = w1 := List.take_append_drop i w1
  have hw2_eq : p1 ++ p2 = w2 := List.take_append_drop j w2
  have hq2 : readWord B (some M) q2 = some H1 := by
    have := hw1.2.2
    rw [← hw1_eq, readWord_append, hq1] at this
    exact this
  have hp2 : readWord B (some M) p2 = some H2 := by
    have := hw2.2.2
    rw [← hw2_eq, readWord_append, hp1] at this
    exact this
  let w2' := p2 ++ p1
  have hw2'_loop : readWord B (some M) w2' = some M := by
    rw [readWord_append, hp2, hp1]
  have hw2'_edges : wordEdges B (some M) w2' = wordEdges B (some H2) w2 := by
    rw [wordEdges_append B hp2, Set.union_comm, ← wordEdges_append B hp1, hw2_eq]
  have hw2'_vis : visited B M w2' = visited B H2 w2 := by
    rw [visited_append B hp2, Set.union_comm, ← visited_append B hp1, hw2_eq]
  let w := (q1 ++ w2') ++ q2
  have hqw2' : readWord B (some H1) (q1 ++ w2') = some M := by
    rw [readWord_append, hq1, hw2'_loop]
  refine ⟨w, ⟨?_, hw1.2.1, ?_⟩, ?_, ?_⟩
  · have hlen1 : q1.length + q2.length = w1.length := by
      simpa using congrArg List.length hw1_eq
    have := hw1.1
    simp [w]; omega
  · rw [readWord_append, hqw2', hq2]
  · rw [wordEdges_append B hqw2', wordEdges_append B hq1, hw2'_edges]
    calc (wordEdges B (some H1) q1 ∪ wordEdges B (some H2) w2) ∪ wordEdges B (some M) q2
        = (wordEdges B (some H1) q1 ∪ wordEdges B (some M) q2) ∪ wordEdges B (some H2) w2 := by
            ext x; simp only [Set.mem_union]; tauto
      _ = wordEdges B (some H1) w1 ∪ wordEdges B (some H2) w2 := by
            rw [← wordEdges_append B hq1, hw1_eq]
  · rw [visited_append B hqw2', visited_append B hq1, hw2'_vis]
    calc (visited B H1 q1 ∪ visited B H2 w2) ∪ visited B M q2
        = (visited B H1 q1 ∪ visited B M q2) ∪ visited B H2 w2 := by
            ext x; simp only [Set.mem_union]; tauto
      _ = visited B H1 w1 ∪ visited B H2 w2 := by
            rw [← visited_append B hq1, hw1_eq]

lemma readWord_trace_init {Q Sigma : Type} {B : NBW Q Sigma}
    {α : ℕ → Sigma} {ρ : ℕ → History Q} (htr : IsTrace B α ρ) :
    ∀ m : ℕ, readWord B (initialHistory B) ((List.range m).map α) = some (ρ m)
  | 0 => by simpa [readWord] using htr.1
  | m + 1 => by
    rw [List.range_succ, List.map_append, List.map_singleton, readWord_append,
      readWord_trace_init htr m]
    simpa [readWord] using htr.2 m

lemma readWord_trace_seg {Q Sigma : Type} {B : NBW Q Sigma}
    {α : ℕ → Sigma} {ρ : ℕ → History Q} (htr : IsTrace B α ρ) (s : ℕ) :
    ∀ len : ℕ, readWord B (some (ρ s)) ((List.range len).map (fun k => α (s + k))) =
      some (ρ (s + len))
  | 0 => by simp [readWord]
  | len + 1 => by
    rw [List.range_succ, List.map_append, List.map_singleton, readWord_append,
      readWord_trace_seg htr s len]
    simpa [readWord, Nat.add_assoc] using htr.2 (s + len)

lemma take_range_map {Sigma : Type} (f : ℕ → Sigma) (len k : ℕ) (hk : k ≤ len) :
    ((List.range len).map f).take k = (List.range k).map f := by
  apply List.ext_getElem
  · simp [hk]
  · intro i h1 h2
    simp

lemma cycle_to_trace {Q Sigma : Type} {B : NBW Q Sigma}
    {D : Set (Edge Q Sigma)} (hD : Cycle B D) :
    ∃ α ρ, IsTrace B α ρ ∧ infSet (edgeSequence α ρ) = D := by
  obtain ⟨H, v, ⟨hv, ⟨u, hu⟩, hloop⟩, rfl⟩ := hD
  let α : ℕ → Sigma := fun t =>
    if h : t < u.length then u[t]
    else v[(t - u.length) % v.length]'(Nat.mod_lt _ hv)
  let pref : ℕ → List Sigma := fun t => (List.range t).map α
  have hpref_succ : ∀ t, pref (t + 1) = pref t ++ [α t] := by
    intro t
    simp [pref, List.range_succ]
  have hpref_u : pref u.length = u := by
    apply List.ext_getElem
    · simp [pref]
    · intro i h1 h2
      simp [pref, α, h2]
  have hpref_loop : ∀ (m : ℕ) (r : ℕ), r ≤ v.length →
      pref (u.length + m * v.length + r) = pref (u.length + m * v.length) ++ v.take r := by
    intro m r hr
    apply List.ext_getElem
    · simp [pref, hr]
    · intro i h1 h2
      by_cases hlt : i < u.length + m * v.length
      · rw [List.getElem_append_left (by simpa [pref] using hlt)]
        simp [pref]
      · have hge : u.length + m * v.length ≤ i := Nat.le_of_not_lt hlt
        rw [List.getElem_append_right (by simpa [pref] using hge)]
        simp only [pref, List.length_map, List.length_range, List.getElem_map,
          List.getElem_range, List.getElem_take]
        have hi_not_u : ¬ i < u.length := by omega
        have hk_lt : i - (u.length + m * v.length) < v.length := by
          simp [pref, hr] at h1
          omega
        have hmod : (i - u.length) % v.length = i - (u.length + m * v.length) := by
          have heq : i - u.length = (i - (u.length + m * v.length)) + m * v.length := by omega
          rw [heq, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hk_lt]
        simp [α, hi_not_u, hmod]
  have hread_mult : ∀ m : ℕ, readWord B (initialHistory B) (pref (u.length + m * v.length)) = some H := by
    intro m
    induction m with
    | zero => simpa [hpref_u] using hu
    | succ m ih =>
      have heq : u.length + (m + 1) * v.length = u.length + m * v.length + v.length := by
        rw [Nat.succ_mul, Nat.add_assoc]
      rw [heq, hpref_loop m v.length le_rfl, List.take_length, readWord_append, ih, hloop]
  have hex : ∀ t : ℕ, ∃ K, readWord B (initialHistory B) (pref t) = some K := by
    intro t
    by_cases hlt : t < u.length
    · have hu_split : pref t ++ u.drop t = u := by
        rw [← hpref_u]
        have htk : (pref u.length).take t = pref t :=
          take_range_map α u.length t (Nat.le_of_lt hlt)
        rw [← htk, hpref_u]
        exact List.take_append_drop t u
      rw [← hu_split] at hu
      exact readWord_some_of_append hu
    · let q := (t - u.length) / v.length
      let r := (t - u.length) % v.length
      have hr_lt : r < v.length := Nat.mod_lt _ hv
      have ht_eq : t = u.length + q * v.length + r := by
        have hdiv := Nat.div_add_mod (t - u.length) v.length
        have hmul : v.length * q = q * v.length := Nat.mul_comm _ _
        change v.length * q + r = t - u.length at hdiv
        omega
      have hv_split : v.take r ++ v.drop r = v := List.take_append_drop r v
      have hread_t : readWord B (initialHistory B) (pref t) = readWord B (some H) (v.take r) := by
        rw [ht_eq, hpref_loop q r (Nat.le_of_lt hr_lt), readWord_append, hread_mult q]
      rw [hread_t]
      rw [← hv_split] at hloop
      exact readWord_some_of_append hloop
  let ρ : ℕ → History Q := fun t => Classical.choose (hex t)
  have hρ : ∀ t, readWord B (initialHistory B) (pref t) = some (ρ t) :=
    fun t => Classical.choose_spec (hex t)
  have htr : IsTrace B α ρ := by
    refine ⟨?_, ?_⟩
    · simpa [pref, readWord] using hρ 0
    · intro t
      have h1 := hρ (t + 1)
      rw [hpref_succ, readWord_append, hρ t] at h1
      simpa [readWord] using h1
  refine ⟨α, ρ, htr, ?_⟩
  ext e
  constructor
  · intro he_inf
    obtain ⟨t, ht_ge, ht_eq⟩ := he_inf u.length
    let q := (t - u.length) / v.length
    let r := (t - u.length) % v.length
    have hr_lt : r < v.length := Nat.mod_lt _ hv
    have ht_decomp : t = u.length + q * v.length + r := by
      have hdiv := Nat.div_add_mod (t - u.length) v.length
      have hmul : v.length * q = q * v.length := Nat.mul_comm _ _
      change v.length * q + r = t - u.length at hdiv
      omega
    have hread_r : readWord B (some H) (v.take r) = some (ρ t) := by
      have h1 := hρ t
      conv_lhs at h1 => rw [ht_decomp]
      rw [hpref_loop q r (Nat.le_of_lt hr_lt), readWord_append, hread_mult q] at h1
      exact h1
    have hα_t : α t = v[r] := by
      have hnot : ¬ t < u.length := by omega
      simp [α, hnot, r]
    rw [← ht_eq]
    refine ⟨⟨r, hr_lt⟩, hread_r, ?_, ?_⟩
    · simpa [Fin.getElem_fin, edgeSequence] using hα_t
    · exact htr.2 t
  · rintro ⟨r, hread_r, hlet, hsucc⟩ N
    let t := u.length + N * v.length + r.val
    have ht_ge : N ≤ t := by
      have : N * 1 ≤ N * v.length := Nat.mul_le_mul_left N hv
      omega
    have hρ_t : ρ t = e.1 := by
      have h1 := hρ t
      rw [hpref_loop N r.val (Nat.le_of_lt r.isLt), readWord_append, hread_mult N, hread_r] at h1
      exact Option.some.inj h1.symm
    have hα_t : α t = e.2.1 := by
      have hnot : ¬ t < u.length := by omega
      have hmod : (t - u.length) % v.length = r.val := by
        have heq : t - u.length = r.val + N * v.length := by omega
        rw [heq, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt r.isLt]
      simp [α, hnot, hmod, hlet]
    have hρ_succ : ρ (t + 1) = e.2.2 := by
      have h2 := htr.2 t
      rw [hρ_t, hα_t, hsucc] at h2
      exact Option.some.inj h2.symm
    refine ⟨t, ht_ge, ?_⟩
    rcases e with ⟨e1, e2, e3⟩
    simp only [edgeSequence] at hρ_t hα_t hρ_succ ⊢
    rw [hρ_t, hα_t, hρ_succ]

end BuchiRabinIndex.LowerBound.Fact31Aux

open BuchiRabinIndex.LowerBound BuchiRabinIndex.LowerBound.Fact31Aux in
theorem solution (n : ℕ) (hn : 1 ≤ n) :
    (∀ D : Set (Edge (Fin n) (Letter n)),
      Cycle (fullBuchi n hn) D ↔
      ∃ α ρ, IsTrace (fullBuchi n hn) α ρ ∧ infSet (edgeSequence α ρ) = D) ∧
    (∀ k (H : Fin k → History (Fin n)) (v : Fin k → List (Letter n)),
      0 < k →
      (∀ i, ClosedWalk (fullBuchi n hn) (H i) (v i)) →
      (∀ j : Fin k, 0 < j.val → ∃ i : Fin k, i.val < j.val ∧
        (visited (fullBuchi n hn) (H i) (v i) ∩
          visited (fullBuchi n hn) (H j) (v j)).Nonempty) →
      Cycle (fullBuchi n hn) (⋃ i, wordEdges (fullBuchi n hn) (some (H i)) (v i))) := by
  classical
  let F := fullBuchi n hn
  refine ⟨?_, ?_⟩
  · intro D
    constructor
    · exact cycle_to_trace
    · rintro ⟨α, ρ, htr, hinf⟩
      have hfinH : Finite (History (Fin n)) := history_finite
      have hfinE : Finite (Edge (Fin n) (Letter n)) := inferInstance
      have hft : Fintype (Edge (Fin n) (Letter n)) := @Fintype.ofFinite _ hfinE
      obtain ⟨N0, hN0⟩ := @eventually_mem_infSet _ hfinE (edgeSequence α ρ)
      obtain ⟨e0, he0⟩ := @infSet_nonempty _ hfinE (edgeSequence α ρ)
      obtain ⟨a, haN0, ha_eq⟩ := he0 N0
      let D_fin : Finset (Edge (Fin n) (Letter n)) :=
        (@Finset.univ _ hft).filter (fun e => e ∈ D)
      have hwit_ex : ∀ e ∈ D, ∃ t ≥ a, edgeSequence α ρ t = e := by
        intro e heD
        rw [← hinf] at heD
        exact heD a
      let wit : Edge (Fin n) (Letter n) → ℕ :=
        fun e => if he : e ∈ D then Classical.choose (hwit_ex e he) else a
      let M := max (a + 1) (D_fin.sup fun e => wit e + 1)
      obtain ⟨b, hbM, hb_eq⟩ := he0 M
      have hab : a < b := by omega
      have hρ_ab : ρ b = ρ a := by
        have h1 : (edgeSequence α ρ a).1 = e0.1 := congrArg Prod.fst ha_eq
        have h2 : (edgeSequence α ρ b).1 = e0.1 := congrArg Prod.fst hb_eq
        exact h2.trans h1.symm
      let v : List (Letter n) := (List.range (b - a)).map (fun k => α (a + k))
      have hv_len : 0 < v.length := by simp [v]; omega
      have hreach : Reachable F (ρ a) :=
        ⟨(List.range a).map α, readWord_trace_init htr a⟩
      have hloop : readWord F (some (ρ a)) v = some (ρ a) := by
        have hseg := readWord_trace_seg htr a (b - a)
        have hab_eq : a + (b - a) = b := by omega
        simpa [v, hab_eq, hρ_ab] using hseg
      refine ⟨ρ a, v, ⟨hv_len, hreach, hloop⟩, ?_⟩
      ext e
      simp only [wordEdges, Set.mem_setOf_eq]
      constructor
      · rintro ⟨i, hread_i, hlet_i, hsucc_i⟩
        have hi_lt : i.val < b - a := by simpa [v] using i.isLt
        have htk : v.take i.val = (List.range i.val).map (fun k => α (a + k)) :=
          take_range_map _ (b - a) i.val (Nat.le_of_lt hi_lt)
        rw [htk, readWord_trace_seg htr a i.val] at hread_i
        have he1 : e.1 = ρ (a + i.val) := Option.some.inj hread_i.symm
        have he2 : e.2.1 = α (a + i.val) := by
          simpa [v] using hlet_i
        have he3 : e.2.2 = ρ (a + i.val + 1) := by
          rw [he1, he2, htr.2 (a + i.val)] at hsucc_i
          exact Option.some.inj hsucc_i.symm
        have he_eq : e = edgeSequence α ρ (a + i.val) := by
          rcases e with ⟨x1, x2, x3⟩
          simp only [edgeSequence] at he1 he2 he3 ⊢
          rw [he1, he2, he3]
        rw [he_eq, ← hinf]
        exact hN0 (a + i.val) (by omega)
      · intro heD
        have he_fin : e ∈ D_fin := Finset.mem_filter.mpr ⟨@Finset.mem_univ _ hft e, heD⟩
        have hwit_spec := Classical.choose_spec (hwit_ex e heD)
        have hwit_eq : wit e = Classical.choose (hwit_ex e heD) := dif_pos heD
        let t := wit e
        have hta : a ≤ t := by simpa [t, hwit_eq] using hwit_spec.1
        have hte : edgeSequence α ρ t = e := by simpa [t, hwit_eq] using hwit_spec.2
        have ht_le_sup : wit e + 1 ≤ D_fin.sup (fun x => wit x + 1) :=
          Finset.le_sup (f := fun x => wit x + 1) he_fin
        have htb : t < b := by omega
        have hk_lt : t - a < v.length := by simp [v]; omega
        refine ⟨⟨t - a, hk_lt⟩, ?_, ?_, ?_⟩
        · have htk : v.take (t - a) = (List.range (t - a)).map (fun k => α (a + k)) :=
            take_range_map _ (b - a) (t - a) (by omega)
          rw [htk, readWord_trace_seg htr a (t - a)]
          have hat : a + (t - a) = t := by omega
          rw [hat, ← hte]
          rfl
        · have hat : a + (t - a) = t := by omega
          simp only [Fin.getElem_fin, v, List.getElem_map, List.getElem_range, hat, ← hte, edgeSequence]
        · rw [← hte]
          exact htr.2 t
  · intro k H v hk hcw hconn
    have hind : ∀ m : ℕ, 1 ≤ m → m ≤ k →
        ∃ w : List (Letter n),
          ClosedWalk F (H ⟨0, hk⟩) w ∧
          wordEdges F (some (H ⟨0, hk⟩)) w =
            (⋃ (i : Fin k) (_ : i.val < m), wordEdges F (some (H i)) (v i)) ∧
          visited F (H ⟨0, hk⟩) w =
            (⋃ (i : Fin k) (_ : i.val < m), visited F (H i) (v i)) := by
      intro m hm1 hmk
      induction m with
      | zero => omega
      | succ m ih =>
        by_cases hm0 : m = 0
        · subst hm0
          refine ⟨v ⟨0, hk⟩, hcw ⟨0, hk⟩, ?_, ?_⟩
          · ext e
            simp only [Set.mem_iUnion]
            constructor
            · intro he
              exact ⟨⟨0, hk⟩, Nat.zero_lt_one, he⟩
            · rintro ⟨i, hi, he⟩
              have hi0 : i = ⟨0, hk⟩ := Fin.ext (by simp; omega)
              rwa [hi0] at he
          · ext K
            simp only [Set.mem_iUnion]
            constructor
            · intro hK
              exact ⟨⟨0, hk⟩, Nat.zero_lt_one, hK⟩
            · rintro ⟨i, hi, hK⟩
              have hi0 : i = ⟨0, hk⟩ := Fin.ext (by simp; omega)
              rwa [hi0] at hK
        · have hm_ge : 1 ≤ m := by omega
          have hm_lt : m < k := by omega
          obtain ⟨w_prev, hcw_prev, hedges_prev, hvis_prev⟩ := ih hm_ge (Nat.le_of_lt hm_lt)
          let j : Fin k := ⟨m, hm_lt⟩
          obtain ⟨i, hi_lt, M, hMi, hMj⟩ := hconn j (by simp [j]; omega)
          have hM_prev : M ∈ visited F (H ⟨0, hk⟩) w_prev := by
            rw [hvis_prev]
            exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨hi_lt, hMi⟩⟩
          obtain ⟨w_new, hcw_new, hedges_new, hvis_new⟩ :=
            splice_closedWalk F hcw_prev (hcw j) hM_prev hMj
          refine ⟨w_new, hcw_new, ?_, ?_⟩
          · rw [hedges_new, hedges_prev]
            ext e
            simp only [Set.mem_union, Set.mem_iUnion]
            constructor
            · rintro (⟨a, ha, he⟩ | he)
              · exact ⟨a, by omega, he⟩
              · exact ⟨j, by simp [j], he⟩
            · rintro ⟨a, ha, he⟩
              by_cases hal : a.val < m
              · exact Or.inl ⟨a, hal, he⟩
              · have haj : a = j := Fin.ext (by simp [j]; omega)
                subst haj
                exact Or.inr he
          · rw [hvis_new, hvis_prev]
            ext K
            simp only [Set.mem_union, Set.mem_iUnion]
            constructor
            · rintro (⟨a, ha, hK⟩ | hK)
              · exact ⟨a, by omega, hK⟩
              · exact ⟨j, by simp [j], hK⟩
            · rintro ⟨a, ha, hK⟩
              by_cases hal : a.val < m
              · exact Or.inl ⟨a, hal, hK⟩
              · have haj : a = j := Fin.ext (by simp [j]; omega)
                subst haj
                exact Or.inr hK
    obtain ⟨w, hcw_w, hedges_w, _⟩ := hind k hk le_rfl
    refine ⟨H ⟨0, hk⟩, w, hcw_w, ?_⟩
    rw [hedges_w]
    ext e
    simp only [Set.mem_iUnion]
    exact ⟨fun ⟨i, _, he⟩ => ⟨i, he⟩, fun ⟨i, he⟩ => ⟨i, i.isLt, he⟩⟩
