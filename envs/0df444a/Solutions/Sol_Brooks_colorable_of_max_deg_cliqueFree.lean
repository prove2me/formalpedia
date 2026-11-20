-- Prove2me | solution 1 for Brooks.colorable_of_max_deg_cliqueFree
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T06:06:50.191888+00:00
-- url     : https://prove2.me/submissions/97aeae2b-4f8a-443f-bba7-cf602a769ef0

import Definitions.Def_opg37271_star_edge_coloring
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Data.Finset.Card

set_option autoImplicit false

open OPG37271

universe u

/-!
# Brooks' Theorem (`Δ ≤ k`, `k ≥ 3`, and Specialization to `Δ ≤ 4`)

We formalize Mariusz Zając's short proof of Brooks' theorem (*A short proof of Brooks' theorem*,
arXiv:1805.11176), which avoids 2-connectivity and block-cutpoint trees entirely by combining
induction on vertex subsets with sequential greedy coloring along uncolored paths (`pathColor`).
-/

/-- `ProperOn G S c` means that `c` assigns distinct colors to adjacent vertices within `S`. -/
private def ProperOn {V : Type u} (G : SimpleGraph V) {k : ℕ}
    (S : Finset V) (c : V → Fin k) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, G.Adj u v → c u ≠ c v

/-- Consecutive vertices of a list are adjacent in `G`. -/
private def IsAdjChain {V : Type u} (G : SimpleGraph V) : List V → Prop
  | [] => True
  | [_] => True
  | x :: y :: rest => G.Adj x y ∧ IsAdjChain G (y :: rest)

private lemma getLast_append_right {α : Type*} :
    ∀ (A B : List α) (hB : B ≠ []) (hAB : A ++ B ≠ []),
      (A ++ B).getLast hAB = B.getLast hB
  | [], _, _, _ => rfl
  | [_], _ :: _, _, _ => rfl
  | _ :: a₂ :: A', B, hB, _ => getLast_append_right (a₂ :: A') B hB (by simp)

private lemma head_append_left {α : Type*} :
    ∀ (A B : List α) (hA : A ≠ []) (hAB : A ++ B ≠ []),
      (A ++ B).head hAB = A.head hA
  | [], _, hA, _ => absurd rfl hA
  | _ :: _, _, _, _ => rfl

private lemma isAdjChain_left_of_append {V : Type u} {G : SimpleGraph V} :
    ∀ (A B : List V), IsAdjChain G (A ++ B) → IsAdjChain G A
  | [], _, _ => trivial
  | [_], _, _ => trivial
  | _ :: y :: A', B, h => ⟨h.1, isAdjChain_left_of_append (y :: A') B h.2⟩

private lemma isAdjChain_right_of_append {V : Type u} {G : SimpleGraph V} :
    ∀ (A B : List V), IsAdjChain G (A ++ B) → IsAdjChain G B
  | [], B, h => h
  | [_], B, h => by
    cases B with
    | nil => trivial
    | cons _ _ => exact h.2
  | _ :: y :: A', B, h => isAdjChain_right_of_append (y :: A') B h.2

private lemma isAdjChain_append {V : Type u} {G : SimpleGraph V} :
    ∀ (A B : List V), IsAdjChain G A → IsAdjChain G B →
      (∀ (ha : A ≠ []) (hb : B ≠ []), G.Adj (A.getLast ha) (B.head hb)) →
      IsAdjChain G (A ++ B)
  | [], B, _, hB, _ => hB
  | [_], [], _, _, _ => trivial
  | [_], _ :: _, _, hB, hlink =>
    ⟨hlink (List.cons_ne_nil _ _) (List.cons_ne_nil _ _), hB⟩
  | _ :: y :: A', B, hA, hB, hlink => by
    refine ⟨hA.1, isAdjChain_append (y :: A') B hA.2 hB ?_⟩
    intro _ hb
    exact hlink (List.cons_ne_nil _ _) hb

private lemma isAdjChain_reverse {V : Type u} {G : SimpleGraph V} :
    ∀ (L : List V), IsAdjChain G L → IsAdjChain G L.reverse
  | [], _ => trivial
  | [_], _ => trivial
  | x :: y :: rest, ⟨hxy, hrest⟩ => by
    rw [List.reverse_cons]
    refine isAdjChain_append (y :: rest).reverse [x] (isAdjChain_reverse (y :: rest) hrest) trivial ?_
    intro ha _
    have hlast : (y :: rest).reverse.getLast ha = y := by
      simp
    rw [hlast]
    exact hxy.symm

private lemma adj_of_isAdjChain_middle {V : Type u} {G : SimpleGraph V} :
    ∀ (A : List V) {x y : V} (B : List V),
      IsAdjChain G (A ++ x :: y :: B) → G.Adj x y
  | [], _, _, _, h => h.1
  | a :: A', _, _, B, h => by
    have htail : IsAdjChain G (A' ++ _ :: _ :: B) :=
      isAdjChain_right_of_append [a] (A' ++ _ :: _ :: B) h
    exact adj_of_isAdjChain_middle A' B htail

/-- Split a list at its first element satisfying `p`. -/
private lemma split_at_first {α : Type*} (p : α → Prop) [DecidablePred p] :
    ∀ (L : List α), (∃ x ∈ L, p x) →
      ∃ L₁ x L₂, L = L₁ ++ x :: L₂ ∧ p x ∧ (∀ y ∈ L₁, ¬ p y)
  | [], ⟨_, hx, _⟩ => absurd hx (List.not_mem_nil)
  | a :: rest, hex => by
    by_cases ha : p a
    · exact ⟨[], a, rest, rfl, ha, fun _ hy => absurd hy (List.not_mem_nil)⟩
    · have hex' : ∃ x ∈ rest, p x := by
        rcases hex with ⟨x, hx, hpx⟩
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact absurd hpx ha
        · exact ⟨x, hx', hpx⟩
      rcases split_at_first p rest hex' with ⟨L₁, x, L₂, rfl, hx, hnone⟩
      refine ⟨a :: L₁, x, L₂, rfl, hx, ?_⟩
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy'
      · exact ha
      · exact hnone y hy'

/-- Split a list at its last element satisfying `p`. -/
private lemma split_at_last {α : Type*} (p : α → Prop) [DecidablePred p] :
    ∀ (L : List α), (∃ x ∈ L, p x) →
      ∃ L₁ x L₂, L = L₁ ++ x :: L₂ ∧ p x ∧ (∀ y ∈ L₂, ¬ p y)
  | [], ⟨_, hx, _⟩ => absurd hx (List.not_mem_nil)
  | a :: rest, hex => by
    by_cases hrest : ∃ x ∈ rest, p x
    · rcases split_at_last p rest hrest with ⟨L₁, x, L₂, rfl, hx, hnone⟩
      exact ⟨a :: L₁, x, L₂, rfl, hx, hnone⟩
    · push Not at hrest
      rcases hex with ⟨x, hx, hpx⟩
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact ⟨[], x, rest, rfl, hpx, hrest⟩
      · exact absurd hpx (hrest x hx')

private lemma card_neighborFinset_le_of_encard_le {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ}
    (hdeg : ∀ v : V, (G.neighborSet v).encard ≤ k) (v : V) :
    (G.neighborFinset v).card ≤ k := by
  have h' : ((G.neighborFinset v : Set V)).encard ≤ k := by
    convert hdeg v using 1
    congr 1
    ext x
    simp
  rw [Set.encard_coe_eq_coe_finsetCard] at h'
  exact Nat.cast_le.mp h'

private lemma exists_color_not_mem_fin {k : ℕ} (used : Finset (Fin k)) (h : used.card < k) :
    ∃ col : Fin k, col ∉ used := by
  by_contra hnone
  push Not at hnone
  have hle := Finset.card_le_card (s := Finset.univ) (fun x _ => hnone x)
  rw [Finset.card_fin] at hle
  omega

/-- Single-vertex greedy coloring extension whenever the colored neighbors of `v` in `T` use
strictly fewer than `k` colors. -/
private lemma extend_properOn_of_card_image_lt {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ}
    {T : Finset V} {c : V → Fin k} (hc : ProperOn G T c)
    {v : V} (hv : v ∉ T)
    (hcard : ((T.filter (G.Adj v)).image c).card < k) :
    ∃ c' : V → Fin k, ProperOn G (insert v T) c' ∧ ∀ x ≠ v, c' x = c x := by
  rcases exists_color_not_mem_fin ((T.filter (G.Adj v)).image c) hcard with ⟨col, hcol⟩
  refine ⟨Function.update c v col, ?_, fun x hx => Function.update_of_ne hx col c⟩
  intro x hx y hy hxy
  have hne : x ≠ y := hxy.ne
  by_cases hxv : x = v
  · subst hxv
    have hyv : y ≠ x := hne.symm
    have hyT : y ∈ T := by
      rcases Finset.mem_insert.mp hy with rfl | hyT
      · exact absurd rfl hyv
      · exact hyT
    rw [Function.update_self, Function.update_of_ne hyv]
    intro heq
    apply hcol
    exact Finset.mem_image.mpr ⟨y, Finset.mem_filter.mpr ⟨hyT, hxy⟩, heq.symm⟩
  · by_cases hyv : y = v
    · subst hyv
      have hxT : x ∈ T := by
        rcases Finset.mem_insert.mp hx with rfl | hxT
        · exact absurd rfl hxv
        · exact hxT
      rw [Function.update_of_ne hxv, Function.update_self]
      intro heq
      apply hcol
      exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hxT, hxy.symm⟩, heq⟩
    · have hxT : x ∈ T := (Finset.mem_insert.mp hx).resolve_left hxv
      have hyT : y ∈ T := (Finset.mem_insert.mp hy).resolve_left hyv
      rw [Function.update_of_ne hxv, Function.update_of_ne hyv]
      exact hc x hxT y hyT hxy

/-- Greedy extension at a vertex `v ∈ S` of degree `< k` in `G[S]`. -/
private lemma extend_properOn_of_deg_lt {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ}
    {S : Finset V} {v : V} (hvS : v ∈ S)
    (hlt : (S.filter (G.Adj v)).card < k)
    {c : V → Fin k} (hc : ProperOn G (S.erase v) c) :
    ∃ c' : V → Fin k, ProperOn G S c' := by
  have hsub : (S.erase v).filter (G.Adj v) ⊆ S.filter (G.Adj v) :=
    Finset.filter_subset_filter _ (Finset.erase_subset v S)
  have himg : (((S.erase v).filter (G.Adj v)).image c).card < k :=
    lt_of_le_of_lt (le_trans Finset.card_image_le (Finset.card_le_card hsub)) hlt
  rcases extend_properOn_of_card_image_lt hc (Finset.notMem_erase v S) himg with ⟨c', hc', _⟩
  rw [Finset.insert_erase hvS] at hc'
  exact ⟨c', hc'⟩

/-- Greedy extension at an uncolored vertex `v ∉ T` that still has an uncolored neighbor `w ∉ T`. -/
private lemma extend_properOn_of_uncolored_neighbor {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ}
    (hdeg : ∀ u : V, (G.neighborFinset u).card ≤ k)
    {T : Finset V} {c : V → Fin k} (hc : ProperOn G T c)
    {v : V} (hv : v ∉ T) (huncol : ∃ w : V, G.Adj v w ∧ w ∉ T) :
    ∃ c' : V → Fin k, ProperOn G (insert v T) c' ∧ ∀ x ∈ T, c' x = c x := by
  rcases huncol with ⟨w, hvw, hwT⟩
  have hw_mem : w ∈ G.neighborFinset v := (SimpleGraph.mem_neighborFinset G v w).mpr hvw
  have hsub : T.filter (G.Adj v) ⊆ (G.neighborFinset v).erase w := by
    intro u hu
    rcases Finset.mem_filter.mp hu with ⟨huT, hvu⟩
    exact Finset.mem_erase.mpr ⟨fun huw => hwT (huw ▸ huT),
      (SimpleGraph.mem_neighborFinset G v u).mpr hvu⟩
  have hcard_lt : ((T.filter (G.Adj v)).image c).card < k := by
    have h1 : (T.filter (G.Adj v)).card ≤ ((G.neighborFinset v).erase w).card :=
      Finset.card_le_card hsub
    have h2 : 1 ≤ (G.neighborFinset v).card := Finset.card_pos.mpr ⟨w, hw_mem⟩
    rw [Finset.card_erase_of_mem hw_mem] at h1
    have h3 := hdeg v
    have h4 : ((T.filter (G.Adj v)).image c).card ≤ (T.filter (G.Adj v)).card :=
      Finset.card_image_le
    omega
  rcases extend_properOn_of_card_image_lt hc hv hcard_lt with ⟨c', hc', hag⟩
  exact ⟨c', hc', fun x hxT => hag x (fun hxv => hv (hxv ▸ hxT))⟩

/-- Greedy extension at an uncolored vertex `v ∉ T` that has two distinct colored neighbors in `T`
receiving the same color. -/
private lemma extend_properOn_of_same_color_neighbors {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ}
    (hdeg : ∀ u : V, (G.neighborFinset u).card ≤ k)
    {T : Finset V} {c : V → Fin k} (hc : ProperOn G T c)
    {v : V} (hv : v ∉ T)
    {x y : V} (hxT : x ∈ T) (hyT : y ∈ T) (hxy : x ≠ y)
    (hvx : G.Adj v x) (hvy : G.Adj v y) (hsame : c x = c y) :
    ∃ c' : V → Fin k, ProperOn G (insert v T) c' := by
  let A : Finset V := T.filter (G.Adj v)
  have hxA : x ∈ A := Finset.mem_filter.mpr ⟨hxT, hvx⟩
  have hyA : y ∈ A := Finset.mem_filter.mpr ⟨hyT, hvy⟩
  have hA_sub : A ⊆ G.neighborFinset v := by
    intro u hu
    exact (SimpleGraph.mem_neighborFinset G v u).mpr (Finset.mem_filter.mp hu).2
  have himg_sub : A.image c ⊆ (A.erase y).image c := by
    intro col hcol
    rcases Finset.mem_image.mp hcol with ⟨u, huA, rfl⟩
    by_cases huy : u = y
    · subst huy
      exact Finset.mem_image.mpr ⟨x, Finset.mem_erase.mpr ⟨hxy, hxA⟩, hsame⟩
    · exact Finset.mem_image.mpr ⟨u, Finset.mem_erase.mpr ⟨huy, huA⟩, rfl⟩
  have hcard_lt : (A.image c).card < k := by
    have h1 : (A.image c).card ≤ ((A.erase y).image c).card := Finset.card_le_card himg_sub
    have h2 : ((A.erase y).image c).card ≤ (A.erase y).card := Finset.card_image_le
    have h3 : 1 ≤ A.card := Finset.card_pos.mpr ⟨y, hyA⟩
    rw [Finset.card_erase_of_mem hyA] at h2
    have h4 : A.card ≤ k := le_trans (Finset.card_le_card hA_sub) (hdeg v)
    omega
  rcases extend_properOn_of_card_image_lt hc hv hcard_lt with ⟨c', hc', _⟩
  exact ⟨c', hc'⟩

/-- Zając's `PathColor(L; z)`: sequentially color all vertices of `L` along an uncolored path
`L ++ [z]`, leaving `z` uncolored and preserving colors already assigned on `T`. -/
private lemma pathColor {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ}
    (hdeg : ∀ u : V, (G.neighborFinset u).card ≤ k)
    {T : Finset V} {c : V → Fin k} (hc : ProperOn G T c)
    (L : List V) (z : V)
    (hnd : (L ++ [z]).Nodup)
    (hdisj : ∀ x ∈ L, x ∉ T)
    (hz : z ∉ T)
    (hchain : IsAdjChain G (L ++ [z])) :
    ∃ c' : V → Fin k, ProperOn G (T ∪ L.toFinset) c' ∧ ∀ x ∈ T, c' x = c x := by
  induction L generalizing T c with
  | nil =>
    exact ⟨c, by simpa using hc, fun _ _ => rfl⟩
  | cons w L' ih =>
    have hwT : w ∉ T := hdisj w (List.mem_cons_self)
    have hne_tail : L' ++ [z] ≠ [] := by simp
    let nxt : V := (L' ++ [z]).head hne_tail
    have htail_eq : L' ++ [z] = nxt :: (L' ++ [z]).tail :=
      (List.cons_head_tail hne_tail).symm
    have hchain_cons : IsAdjChain G (w :: nxt :: (L' ++ [z]).tail) := by
      simpa [List.cons_append, ← htail_eq] using hchain
    have hwnxt : G.Adj w nxt := hchain_cons.1
    have hchain' : IsAdjChain G (L' ++ [z]) := by
      rw [htail_eq]
      exact hchain_cons.2
    have hnxt_mem : nxt ∈ L' ++ [z] := List.head_mem hne_tail
    have hnxt_not_T : nxt ∉ T := by
      rcases List.mem_append.mp hnxt_mem with hL' | hz'
      · exact hdisj nxt (List.mem_cons_of_mem w hL')
      · rw [List.mem_singleton.mp hz']
        exact hz
    rcases extend_properOn_of_uncolored_neighbor hdeg hc hwT ⟨nxt, hwnxt, hnxt_not_T⟩ with
      ⟨c₁, hc₁, hag₁⟩
    rw [List.cons_append, List.nodup_cons] at hnd
    rcases hnd with ⟨hw_not_tail, hnd'⟩
    have hdisj' : ∀ x ∈ L', x ∉ insert w T := by
      intro x hxL' hmem
      rcases Finset.mem_insert.mp hmem with rfl | hxT
      · exact hw_not_tail (List.mem_append_left [z] hxL')
      · exact hdisj x (List.mem_cons_of_mem w hxL') hxT
    have hz' : z ∉ insert w T := by
      intro hmem
      rcases Finset.mem_insert.mp hmem with rfl | hzT
      · exact hw_not_tail (List.mem_append_right L' (List.mem_singleton_self z))
      · exact hz hzT
    rcases ih hc₁ hnd' hdisj' hz' hchain' with ⟨c₂, hc₂, hag₂⟩
    have hset : insert w T ∪ L'.toFinset = T ∪ (w :: L').toFinset := by
      ext u
      simp only [Finset.mem_union, Finset.mem_insert, List.toFinset_cons]
      tauto
    rw [hset] at hc₂
    refine ⟨c₂, hc₂, ?_⟩
    intro x hxT
    rw [hag₂ x (Finset.mem_insert_of_mem hxT), hag₁ x hxT]

/-- If `G` is `(k + 1)`-clique-free and `v ∈ S` has `k` neighbors in `S`, two of those neighbors
are non-adjacent. -/
private lemma exists_nonadj_neighbors {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ}
    (hnoK : G.CliqueFree (k + 1)) {S : Finset V} {v : V}
    (hcard : (S.filter (G.Adj v)).card = k) :
    ∃ x ∈ S.filter (G.Adj v), ∃ y ∈ S.filter (G.Adj v), x ≠ y ∧ ¬ G.Adj x y := by
  let N := S.filter (G.Adj v)
  by_contra hall
  push Not at hall
  have hN_clique : G.IsNClique k N := by
    rw [SimpleGraph.isNClique_iff]
    refine ⟨?_, hcard⟩
    intro x hx y hy hne
    exact hall x hx y hy hne
  have hv_adj : ∀ b ∈ N, G.Adj v b := fun b hb => (Finset.mem_filter.mp hb).2
  exact hnoK (insert v N) (hN_clique.insert hv_adj)

/-- Extend any simple path `P` in `S` to a maximal simple path `P'` in `S` whose last vertex has
all its `S`-neighbors already on `P'`. -/
private lemma extend_to_maximal_path {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (S : Finset V) :
    ∀ (m : ℕ) (P : List V) (_ : P ≠ []),
      S.card - P.length ≤ m →
      P.Nodup → (∀ w ∈ P, w ∈ S) → IsAdjChain G P →
      ∃ (P' : List V) (hne' : P' ≠ []),
        P <+: P' ∧ P'.Nodup ∧ (∀ w ∈ P', w ∈ S) ∧ IsAdjChain G P' ∧
        (∀ u ∈ S, G.Adj (P'.getLast hne') u → u ∈ P') := by
  intro m
  induction m with
  | zero =>
    intro P hne hrem hnd hsub hchain
    refine ⟨P, hne, List.prefix_refl P, hnd, hsub, hchain, ?_⟩
    intro u huS hadj
    by_contra hunot
    have htoSub : insert u P.toFinset ⊆ S := by
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hzP
      · exact huS
      · exact hsub z (List.mem_toFinset.mp hzP)
    have hcard_ins : (insert u P.toFinset).card ≤ S.card := Finset.card_le_card htoSub
    rw [Finset.card_insert_of_notMem (by simpa using hunot), List.toFinset_card_of_nodup hnd] at hcard_ins
    omega
  | succ m ih =>
    intro P hne hrem hnd hsub hchain
    by_cases hex : ∃ u ∈ S, G.Adj (P.getLast hne) u ∧ u ∉ P
    · rcases hex with ⟨u, huS, hadj, hunot⟩
      let P₁ := P ++ [u]
      have hne₁ : P₁ ≠ [] := by simp [P₁]
      have hnd₁ : P₁.Nodup := by
        rw [List.nodup_append]
        refine ⟨hnd, List.nodup_singleton u, ?_⟩
        intro z hzP w hwu hzw
        rw [List.mem_singleton] at hwu
        subst hwu
        exact hunot (hzw ▸ hzP)
      have hsub₁ : ∀ w ∈ P₁, w ∈ S := by
        intro w hw
        rcases List.mem_append.mp hw with hwP | hwu
        · exact hsub w hwP
        · rw [List.mem_singleton.mp hwu]
          exact huS
      have hchain₁ : IsAdjChain G P₁ := by
        refine isAdjChain_append P [u] hchain trivial ?_
        intro _ _
        exact hadj
      have hlen_le : P₁.length ≤ S.card := by
        have htoSub : P₁.toFinset ⊆ S := fun z hz => hsub₁ z (List.mem_toFinset.mp hz)
        have hc := Finset.card_le_card htoSub
        rwa [List.toFinset_card_of_nodup hnd₁] at hc
      have hrem₁ : S.card - P₁.length ≤ m := by
        simp only [P₁, List.length_append, List.length_singleton] at hlen_le ⊢
        omega
      rcases ih P₁ hne₁ hrem₁ hnd₁ hsub₁ hchain₁ with
        ⟨P', hne', hpref₁, hnd', hsub', hchain', hmax⟩
      exact ⟨P', hne', (List.prefix_append P [u]).trans hpref₁, hnd', hsub', hchain', hmax⟩
    · refine ⟨P, hne, List.prefix_refl P, hnd, hsub, hchain, ?_⟩
      intro u huS hadj
      by_contra hunot
      exact hex ⟨u, huS, hadj, hunot⟩

/-- Zając Case 1: the maximal path `P` starting with `[x, v, y]` covers all vertices of `S`. -/
private lemma color_case1_hamiltonian {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ} (hk : 3 ≤ k)
    (hdeg : ∀ u : V, (G.neighborFinset u).card ≤ k)
    {S : Finset V} {x v y : V} {P : List V}
    (hpref : [x, v, y] <+: P) (hnd : P.Nodup) (hfull : P.toFinset = S)
    (hchain : IsAdjChain G P)
    (hvx : G.Adj v x) (hvy : G.Adj v y) (hnxy : ¬ G.Adj x y)
    (hreg_v : (S.filter (G.Adj v)).card = k) :
    ∃ c : V → Fin k, ProperOn G S c := by
  rcases hpref with ⟨R, rfl⟩
  -- Pick a third neighbor `w` of `v` in `S` distinct from `x` and `y`.
  have hex_w : ∃ w ∈ S.filter (G.Adj v), w ≠ x ∧ w ≠ y := by
    have hcard_sdiff : ((S.filter (G.Adj v)) \ {x, y}).Nonempty := by
      apply Finset.card_pos.mp
      have hle_xy : ({x, y} : Finset V).card ≤ 2 := Finset.card_le_two
      have hle_sd := Finset.le_card_sdiff ({x, y} : Finset V) (S.filter (G.Adj v))
      omega
    rcases hcard_sdiff with ⟨w, hw⟩
    rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hw
    exact ⟨w, hw.1, hw.2⟩
  rcases hex_w with ⟨w, hw_filt, hwx, hwy⟩
  rcases Finset.mem_filter.mp hw_filt with ⟨hwS, hvw⟩
  have hwv : w ≠ v := hvw.ne.symm
  have hwP : w ∈ [x, v, y] ++ R := List.mem_toFinset.mp (hfull ▸ hwS)
  have hwR : w ∈ R := by
    simp only [List.cons_append, List.nil_append, List.mem_cons] at hwP
    rcases hwP with rfl | rfl | rfl | hwR
    · exact absurd rfl hwx
    · exact absurd rfl hwv
    · exact absurd rfl hwy
    · exact hwR
  rcases List.append_of_mem hwR with ⟨R₁, R₂, rfl⟩
  -- Unpack Nodup of `x :: v :: y :: (R₁ ++ w :: R₂)`
  simp only [List.cons_append, List.nil_append] at hnd hfull
  rw [List.nodup_cons] at hnd; rcases hnd with ⟨hx_rest, hnd_vy⟩
  rw [List.nodup_cons] at hnd_vy; rcases hnd_vy with ⟨hv_rest, hnd_y⟩
  rw [List.nodup_cons] at hnd_y; rcases hnd_y with ⟨hy_rest, hnd_R⟩
  have hxy_ne : x ≠ y := fun h => hx_rest (by simp [h])
  -- Step 1: Give `x` and `y` the same color `0`.
  let T₀ : Finset V := {x, y}
  let c₀ : V → Fin k := fun _ => ⟨0, by omega⟩
  have hc₀ : ProperOn G T₀ c₀ := by
    intro a ha b hb hab
    simp only [T₀, Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact absurd rfl hab.ne
    · exact absurd hab hnxy
    · exact absurd hab.symm hnxy
    · exact absurd rfl hab.ne
  -- Step 2: `PathColor(R₁; w)`
  have hR_eq : R₁ ++ w :: R₂ = (R₁ ++ [w]) ++ R₂ := by simp
  have hnd_R₁w : (R₁ ++ [w]).Nodup := by
    rw [hR_eq, List.nodup_append] at hnd_R
    exact hnd_R.1
  have hchain_R : IsAdjChain G (R₁ ++ w :: R₂) :=
    isAdjChain_right_of_append [x, v, y] (R₁ ++ w :: R₂) hchain
  have hchain_R₁w : IsAdjChain G (R₁ ++ [w]) := by
    rw [hR_eq] at hchain_R
    exact isAdjChain_left_of_append (R₁ ++ [w]) R₂ hchain_R
  have hdisj₁ : ∀ u ∈ R₁, u ∉ T₀ := by
    intro u hu hmem
    simp only [T₀, Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl
    · exact hx_rest (by simp [hu])
    · exact hy_rest (by simp [hu])
  have hw_not_T₀ : w ∉ T₀ := by
    simp [T₀, hwx, hwy]
  rcases pathColor hdeg hc₀ R₁ w hnd_R₁w hdisj₁ hw_not_T₀ hchain_R₁w with ⟨c₁, hc₁, hag₁⟩
  -- Step 3: `PathColor(R₂.reverse ++ [w]; v)`
  let T₁ : Finset V := T₀ ∪ R₁.toFinset
  let L₂ : List V := (w :: R₂).reverse
  have hnd_wR₂ : (w :: R₂).Nodup := by
    rw [List.nodup_append] at hnd_R
    exact hnd_R.2.1
  have hdisj_R₁_wR₂ : ∀ u ∈ R₁, u ∉ w :: R₂ := by
    rw [List.nodup_append] at hnd_R
    exact fun u hu hwR₂ => hnd_R.2.2 u hu u hwR₂ rfl
  have hnd_L₂v : (L₂ ++ [v]).Nodup := by
    rw [List.nodup_append]
    refine ⟨List.nodup_reverse.mpr hnd_wR₂, List.nodup_singleton v, ?_⟩
    intro u hu z hzv huz
    rw [List.mem_singleton] at hzv
    subst hzv
    subst huz
    rw [List.mem_reverse] at hu
    exact hv_rest (List.mem_cons_of_mem y (List.mem_append_right R₁ hu))
  have hdisj₂ : ∀ u ∈ L₂, u ∉ T₁ := by
    intro u hu hmem
    rw [List.mem_reverse] at hu
    simp only [T₁, T₀, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
      List.mem_toFinset] at hmem
    rcases hmem with (rfl | rfl) | huR₁
    · exact hx_rest (List.mem_cons_of_mem v (List.mem_cons_of_mem y (List.mem_append_right R₁ hu)))
    · exact hy_rest (List.mem_append_right R₁ hu)
    · exact hdisj_R₁_wR₂ u huR₁ hu
  have hv_not_T₁ : v ∉ T₁ := by
    simp only [T₁, T₀, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
      List.mem_toFinset, not_or]
    refine ⟨⟨fun hvx_eq => hx_rest (by simp [hvx_eq.symm]),
      fun hvy_eq => hv_rest (by simp [hvy_eq])⟩, ?_⟩
    intro hvR₁
    exact hv_rest (List.mem_cons_of_mem y (List.mem_append_left _ hvR₁))
  have hchain_wR₂ : IsAdjChain G (w :: R₂) :=
    isAdjChain_right_of_append R₁ (w :: R₂) hchain_R
  have hchain_L₂v : IsAdjChain G (L₂ ++ [v]) := by
    refine isAdjChain_append L₂ [v] (isAdjChain_reverse (w :: R₂) hchain_wR₂) trivial ?_
    intro ha _
    have hlast : (w :: R₂).reverse.getLast ha = w := by
      simp
    rw [hlast]
    exact hvw.symm
  rcases pathColor hdeg hc₁ L₂ v hnd_L₂v hdisj₂ hv_not_T₁ hchain_L₂v with ⟨c₂, hc₂, hag₂⟩
  -- Step 4: Color `v`, whose neighbors `x` and `y` still share color `0`.
  let T₂ : Finset V := T₁ ∪ L₂.toFinset
  have hv_not_T₂ : v ∉ T₂ := by
    simp only [T₂, Finset.mem_union, List.mem_toFinset, L₂, List.mem_reverse, not_or]
    exact ⟨hv_not_T₁, fun hvwR₂ => hv_rest (List.mem_cons_of_mem y (List.mem_append_right R₁ hvwR₂))⟩
  have hx_mem_T₁ : x ∈ T₁ := Finset.mem_union_left _ (by simp [T₀])
  have hy_mem_T₁ : y ∈ T₁ := Finset.mem_union_left _ (by simp [T₀])
  have hx_mem_T₂ : x ∈ T₂ := Finset.mem_union_left _ hx_mem_T₁
  have hy_mem_T₂ : y ∈ T₂ := Finset.mem_union_left _ hy_mem_T₁
  have hsame : c₂ x = c₂ y := by
    rw [hag₂ x hx_mem_T₁, hag₂ y hy_mem_T₁, hag₁ x (by simp [T₀]), hag₁ y (by simp [T₀])]
  rcases extend_properOn_of_same_color_neighbors hdeg hc₂ hv_not_T₂
      hx_mem_T₂ hy_mem_T₂ hxy_ne hvx hvy hsame with ⟨c₃, hc₃⟩
  have hins_eq : insert v T₂ = S := by
    rw [← hfull]
    ext z
    simp only [T₂, T₁, T₀, L₂, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton,
      List.toFinset_cons, List.mem_toFinset, List.mem_append, List.mem_reverse, List.mem_cons]
    tauto
  rw [hins_eq] at hc₃
  exact ⟨c₃, hc₃⟩

/-- Zając Case 2: `P.toFinset ⊂ S`, so the tail of `P` from the first neighbor of `v_r` forms a
proper induced subgraph `C` with `C.card ≤ P.toFinset.card < S.card`. -/
private lemma color_case2_cycle {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ} (hk : 3 ≤ k)
    (hdeg : ∀ u : V, (G.neighborFinset u).card ≤ k)
    {n : ℕ} (ih : ∀ S' : Finset V, S'.card ≤ n → ∃ c : V → Fin k, ProperOn G S' c)
    {S : Finset V} (hScard : S.card = n + 1)
    {P : List V} (hne : P ≠ []) (hnd : P.Nodup) (hsub : ∀ w ∈ P, w ∈ S)
    (hchain : IsAdjChain G P)
    (hmax : ∀ u ∈ S, G.Adj (P.getLast hne) u → u ∈ P)
    (hreg_last : (S.filter (G.Adj (P.getLast hne))).card = k)
    (hP_lt : P.toFinset.card ≤ n) :
    ∃ c : V → Fin k, ProperOn G S c := by
  let v_r : V := P.getLast hne
  have hex_nb : ∃ w ∈ P, G.Adj v_r w := by
    have hpos : (S.filter (G.Adj v_r)).Nonempty :=
      Finset.card_pos.mp (by dsimp [v_r]; omega)
    rcases hpos with ⟨w, hw⟩
    rcases Finset.mem_filter.mp hw with ⟨hwS, hadj⟩
    exact ⟨w, hmax w hwS hadj, hadj⟩
  rcases split_at_first (G.Adj v_r) P hex_nb with ⟨P₁, v_j, C_rest, hP_eq, hadj_rj, hno_P₁⟩
  let C_list : List V := v_j :: C_rest
  let C : Finset V := C_list.toFinset
  let S' : Finset V := S \ C
  have hC_sub_P : C ⊆ P.toFinset := by
    intro z hz
    rw [List.mem_toFinset] at hz ⊢
    rw [hP_eq]
    exact List.mem_append_right P₁ hz
  have hC_sub_S : C ⊆ S := fun z hz => hsub z (List.mem_toFinset.mp (hC_sub_P hz))
  have hC_card_pos : 0 < C.card := Finset.card_pos.mpr ⟨v_j, by simp [C, C_list]⟩
  have hS'_card_le : S'.card ≤ n := by
    have hsd : S'.card = S.card - C.card := by
      dsimp [S']
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hC_sub_S]
    omega
  have hC_card_le : C.card ≤ n := le_trans (Finset.card_le_card hC_sub_P) hP_lt
  -- Inductively color `S' = S \ C`.
  rcases ih S' hS'_card_le with ⟨c₀, hc₀⟩
  -- Subcase 2a vs 2b: is there any edge between `C` and `S'`?
  by_cases hex_cross : ∃ w ∈ C_list, ∃ u ∈ S', G.Adj w u
  · -- Subcase 2b: pick the LAST vertex `v_l` along `C_list` that has a neighbor `u ∈ S'`.
    rcases split_at_last (fun w => ∃ u ∈ S', G.Adj w u) C_list hex_cross with
      ⟨Q₁, v_l, Q₂, hC_eq, ⟨u, huS', hadj_lu⟩, hno_Q₂⟩
    -- Notice `v_r` is the last element of `C_list` and has NO neighbor in `S'`.
    have hvr_last_C : C_list.getLast (List.cons_ne_nil _ _) = v_r := by
      have h := getLast_append_right P₁ C_list (List.cons_ne_nil v_j C_rest) (by simp [C_list])
      have hP_last : (P₁ ++ C_list).getLast (by simp [C_list]) = v_r := by
        dsimp [v_r, C_list]
        congr 1
        exact hP_eq.symm
      exact h.symm.trans hP_last
    have hvr_no_S' : ∀ u' ∈ S', ¬ G.Adj v_r u' := by
      intro u' hu' hadj'
      rcases Finset.mem_sdiff.mp hu' with ⟨hu'S, hu'notC⟩
      have hu'P : u' ∈ P := hmax u' hu'S hadj'
      rw [hP_eq, List.mem_append] at hu'P
      rcases hu'P with hu'P₁ | hu'C
      · exact hno_P₁ u' hu'P₁ hadj'
      · exact hu'notC (List.mem_toFinset.mpr hu'C)
    -- Hence `Q₂` cannot be empty (otherwise `v_l = v_r`, impossible).
    cases Q₂ with
    | nil =>
      have hvl_eq_vr : v_l = v_r := by
        have hlast_Q : (Q₁ ++ [v_l]).getLast (by simp) = v_l := List.getLast_concat
        have hC_last_Q : C_list.getLast (List.cons_ne_nil _ _) = (Q₁ ++ [v_l]).getLast (by simp) := by
          congr 1
        exact hlast_Q.symm.trans (hC_last_Q.symm.trans hvr_last_C)
      exact absurd hadj_lu (hvl_eq_vr ▸ hvr_no_S' u huS')
    | cons v_next Q₃ =>
      have hnd_C : C_list.Nodup := by
        rw [hP_eq, List.nodup_append] at hnd
        exact hnd.2.1
      have hchain_C : IsAdjChain G C_list := by
        rw [hP_eq] at hchain
        exact isAdjChain_right_of_append P₁ C_list hchain
      -- `v_next` has no neighbors in `S'`, so give `v_next` the same color `c₀ u`.
      have hvnext_in_C : v_next ∈ C := by
        rw [List.mem_toFinset, hC_eq]
        simp
      have hvnext_not_S' : v_next ∉ S' := fun h => (Finset.mem_sdiff.mp h).2 hvnext_in_C
      have hvnext_no_S' : ∀ w ∈ S', ¬ G.Adj v_next w :=
        fun w hw hadj => hno_Q₂ v_next List.mem_cons_self ⟨w, hw, hadj⟩
      let T₁ : Finset V := insert v_next S'
      let c₁ : V → Fin k := Function.update c₀ v_next (c₀ u)
      have hc₁ : ProperOn G T₁ c₁ := by
        intro a ha b hb hab
        have hne : a ≠ b := hab.ne
        by_cases ha_vn : a = v_next
        · subst ha_vn
          have hbS' : b ∈ S' := (Finset.mem_insert.mp hb).resolve_left hne.symm
          exact absurd hab (hvnext_no_S' b hbS')
        · by_cases hb_vn : b = v_next
          · subst hb_vn
            have haS' : a ∈ S' := (Finset.mem_insert.mp ha).resolve_left ha_vn
            exact absurd hab.symm (hvnext_no_S' a haS')
          · have haS' : a ∈ S' := (Finset.mem_insert.mp ha).resolve_left ha_vn
            have hbS' : b ∈ S' := (Finset.mem_insert.mp hb).resolve_left hb_vn
            simp only [c₁, Function.update_of_ne ha_vn, Function.update_of_ne hb_vn]
            exact hc₀ a haS' b hbS' hab
      -- Prepare `PathColor(Q₃ ++ Q₁; v_l)`.
      let L : List V := Q₃ ++ Q₁
      have hC_split : C_list = (Q₁ ++ [v_l]) ++ (v_next :: Q₃) := by
        simp [hC_eq]
      have hnd_split := hnd_C
      rw [hC_split, List.nodup_append] at hnd_split
      rcases hnd_split with ⟨hnd_Q₁l, hnd_vnQ₃, hdisj_Q₁l_vnQ₃⟩
      rw [List.nodup_cons] at hnd_vnQ₃
      rcases hnd_vnQ₃ with ⟨hvn_not_Q₃, hnd_Q₃⟩
      have hL_tail : L ++ [v_l] = Q₃ ++ (Q₁ ++ [v_l]) := by simp [L]
      have hnd_Ll : (L ++ [v_l]).Nodup := by
        rw [hL_tail, List.nodup_append]
        refine ⟨hnd_Q₃, hnd_Q₁l, ?_⟩
        intro z hzQ₃ w hwQ₁l hzw
        subst hzw
        exact hdisj_Q₁l_vnQ₃ z hwQ₁l z (List.mem_cons_of_mem v_next hzQ₃) rfl
      have hdisj_L : ∀ z ∈ L, z ∉ T₁ := by
        intro z hzL hmem
        have hzC : z ∈ C := by
          rw [List.mem_toFinset, hC_split]
          rcases List.mem_append.mp hzL with hzQ₃ | hzQ₁
          · exact List.mem_append_right _ (List.mem_cons_of_mem v_next hzQ₃)
          · exact List.mem_append_left _ (List.mem_append_left [v_l] hzQ₁)
        rcases Finset.mem_insert.mp hmem with rfl | hzS'
        · rcases List.mem_append.mp hzL with hzQ₃ | hzQ₁
          · exact hvn_not_Q₃ hzQ₃
          · exact hdisj_Q₁l_vnQ₃ z (List.mem_append_left [v_l] hzQ₁) z List.mem_cons_self rfl
        · exact (Finset.mem_sdiff.mp hzS').2 hzC
      have hvl_in_C : v_l ∈ C := by
        rw [List.mem_toFinset, hC_eq]
        simp
      have hvl_not_T₁ : v_l ∉ T₁ := by
        intro hmem
        rcases Finset.mem_insert.mp hmem with rfl | hvlS'
        · exact hdisj_Q₁l_vnQ₃ v_l (List.mem_append_right Q₁ (List.mem_singleton_self _))
            v_l List.mem_cons_self rfl
        · exact (Finset.mem_sdiff.mp hvlS').2 hvl_in_C
      have hchain_Q₁l : IsAdjChain G (Q₁ ++ [v_l]) := by
        rw [hC_split] at hchain_C
        exact isAdjChain_left_of_append (Q₁ ++ [v_l]) (v_next :: Q₃) hchain_C
      have hchain_Q₃ : IsAdjChain G Q₃ := by
        rw [hC_split] at hchain_C
        exact isAdjChain_right_of_append [v_next] Q₃
          (isAdjChain_right_of_append (Q₁ ++ [v_l]) (v_next :: Q₃) hchain_C)
      have hchain_Ll : IsAdjChain G (L ++ [v_l]) := by
        rw [hL_tail]
        cases Q₃ with
        | nil => simp [hchain_Q₁l]
        | cons q Q₃' =>
          refine isAdjChain_append (q :: Q₃') (Q₁ ++ [v_l]) hchain_Q₃ hchain_Q₁l ?_
          intro hq_ne hQ₁l_ne
          have hlast_eq : (q :: Q₃').getLast hq_ne = v_r := by
            rw [← hvr_last_C]
            have h1 : ((Q₁ ++ [v_l]) ++ (v_next :: q :: Q₃')).getLast (by simp) =
                (v_next :: q :: Q₃').getLast (List.cons_ne_nil _ _) :=
              getLast_append_right (Q₁ ++ [v_l]) (v_next :: q :: Q₃') (List.cons_ne_nil _ _) (by simp)
            have h2 : C_list.getLast (List.cons_ne_nil _ _) =
                ((Q₁ ++ [v_l]) ++ (v_next :: q :: Q₃')).getLast (by simp) := by
              congr 1
            rw [h2, h1]
            rfl
          have hhead_eq : (Q₁ ++ [v_l]).head hQ₁l_ne = v_j := by
            have h1 : C_list.head (List.cons_ne_nil _ _) = v_j := rfl
            have h2 : C_list.head (List.cons_ne_nil _ _) =
                ((Q₁ ++ [v_l]) ++ (v_next :: q :: Q₃')).head (by simp) := by
              congr 1
            have h3 : ((Q₁ ++ [v_l]) ++ (v_next :: q :: Q₃')).head (by simp) =
                (Q₁ ++ [v_l]).head hQ₁l_ne :=
              head_append_left (Q₁ ++ [v_l]) (v_next :: q :: Q₃') hQ₁l_ne (by simp)
            exact h3.symm.trans (h2.symm.trans h1)
          rw [hlast_eq, hhead_eq]
          exact hadj_rj
      rcases pathColor hdeg hc₁ L v_l hnd_Ll hdisj_L hvl_not_T₁ hchain_Ll with ⟨c₂, hc₂, hag₂⟩
      -- Finally color `v_l`, whose neighbors `u` and `v_next` share color `c₀ u`.
      let T₂ : Finset V := T₁ ∪ L.toFinset
      have hvl_not_T₂ : v_l ∉ T₂ := by
        simp only [T₂, Finset.mem_union, List.mem_toFinset, not_or]
        refine ⟨hvl_not_T₁, ?_⟩
        intro hvlL
        rw [List.nodup_append] at hnd_Ll
        exact hnd_Ll.2.2 v_l hvlL v_l (List.mem_singleton_self v_l) rfl
      have hu_mem_T₁ : u ∈ T₁ := Finset.mem_insert_of_mem huS'
      have hvn_mem_T₁ : v_next ∈ T₁ := Finset.mem_insert_self v_next S'
      have hu_mem_T₂ : u ∈ T₂ := Finset.mem_union_left _ hu_mem_T₁
      have hvn_mem_T₂ : v_next ∈ T₂ := Finset.mem_union_left _ hvn_mem_T₁
      have hu_ne_vn : u ≠ v_next := fun h => hvnext_not_S' (h ▸ huS')
      have hadj_l_vn : G.Adj v_l v_next := by
        rw [hC_eq] at hchain_C
        exact adj_of_isAdjChain_middle Q₁ Q₃ hchain_C
      have hsame : c₂ u = c₂ v_next := by
        rw [hag₂ u hu_mem_T₁, hag₂ v_next hvn_mem_T₁]
        simp only [c₁, Function.update_of_ne hu_ne_vn, Function.update_self]
      rcases extend_properOn_of_same_color_neighbors hdeg hc₂ hvl_not_T₂
          hu_mem_T₂ hvn_mem_T₂ hu_ne_vn hadj_lu hadj_l_vn hsame with ⟨c₃, hc₃⟩
      have hins_eq : insert v_l T₂ = S := by
        ext z
        simp only [T₂, T₁, S', L, Finset.mem_insert, Finset.mem_union, Finset.mem_sdiff,
          List.mem_toFinset, List.mem_append]
        constructor
        · rintro (rfl | ((rfl | ⟨hzS, _⟩) | (hzQ₃ | hzQ₁)))
          · exact hC_sub_S hvl_in_C
          · exact hC_sub_S hvnext_in_C
          · exact hzS
          · exact hC_sub_S (by rw [List.mem_toFinset, hC_eq]; simp [hzQ₃])
          · exact hC_sub_S (by rw [List.mem_toFinset, hC_eq]; simp [hzQ₁])
        · intro hzS
          by_cases hzC : z ∈ C
          · rw [List.mem_toFinset, hC_eq, List.mem_append, List.mem_cons, List.mem_cons] at hzC
            tauto
          · exact Or.inr (Or.inl (Or.inr ⟨hzS, hzC⟩))
      rw [hins_eq] at hc₃
      exact ⟨c₃, hc₃⟩
  · -- Subcase 2a: no edge between `C` and `S'`; color `C` by IH and combine disjointly!
    push Not at hex_cross
    rcases ih C hC_card_le with ⟨cC, hcC⟩
    refine ⟨fun z => if z ∈ C then cC z else c₀ z, ?_⟩
    intro a ha b hb hab
    by_cases haC : a ∈ C <;> by_cases hbC : b ∈ C
    · simp only [if_pos haC, if_pos hbC]
      exact hcC a haC b hbC hab
    · exact absurd hab (hex_cross a (List.mem_toFinset.mp haC) b (Finset.mem_sdiff.mpr ⟨hb, hbC⟩))
    · exact absurd hab.symm
        (hex_cross b (List.mem_toFinset.mp hbC) a (Finset.mem_sdiff.mpr ⟨ha, haC⟩))
    · simp only [if_neg haC, if_neg hbC]
      exact hc₀ a (Finset.mem_sdiff.mpr ⟨ha, haC⟩) b (Finset.mem_sdiff.mpr ⟨hb, hbC⟩) hab

/-- Main strong induction on `S.card` for Zając's proof of Brooks' theorem. -/
private lemma brooks_properOn {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} (hk : 3 ≤ k)
    (hdeg : ∀ v : V, (G.neighborFinset v).card ≤ k)
    (hnoK : G.CliqueFree (k + 1)) :
    ∀ (n : ℕ) (S : Finset V), S.card ≤ n → ∃ c : V → Fin k, ProperOn G S c := by
  intro n
  induction n with
  | zero =>
    intro S hS
    have hS0 : S = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hS)
    subst hS0
    exact ⟨fun _ => ⟨0, by omega⟩, fun _ hu => absurd hu (Finset.notMem_empty _)⟩
  | succ n ih =>
    intro S hS
    by_cases hle : S.card ≤ n
    · exact ih S hle
    · have hScard : S.card = n + 1 := by omega
      -- If any vertex in `S` has degree `< k` in `G[S]`, delete it and extend greedily.
      by_cases hex_lt : ∃ v ∈ S, (S.filter (G.Adj v)).card < k
      · rcases hex_lt with ⟨v, hvS, hlt⟩
        have herase : (S.erase v).card ≤ n := by
          rw [Finset.card_erase_of_mem hvS, hScard]
          omega
        rcases ih (S.erase v) herase with ⟨c₀, hc₀⟩
        exact extend_properOn_of_deg_lt hvS hlt hc₀
      · -- Otherwise `G[S]` is `k`-regular.
        push Not at hex_lt
        have hreg : ∀ v ∈ S, (S.filter (G.Adj v)).card = k := by
          intro v hvS
          have hsub_nb : S.filter (G.Adj v) ⊆ G.neighborFinset v := by
            intro u hu
            exact (SimpleGraph.mem_neighborFinset G v u).mpr (Finset.mem_filter.mp hu).2
          have hle_k : (S.filter (G.Adj v)).card ≤ k :=
            le_trans (Finset.card_le_card hsub_nb) (hdeg v)
          have hge_k : k ≤ (S.filter (G.Adj v)).card := hex_lt v hvS
          omega
        have hS_nonempty : S.Nonempty := Finset.card_pos.mp (by omega)
        rcases hS_nonempty with ⟨v, hvS⟩
        rcases exists_nonadj_neighbors hnoK (hreg v hvS) with
          ⟨x, hx_filt, y, hy_filt, hxy_ne, hnxy⟩
        rcases Finset.mem_filter.mp hx_filt with ⟨hxS, hvx⟩
        rcases Finset.mem_filter.mp hy_filt with ⟨hyS, hvy⟩
        -- Build a maximal path `P` in `S` starting with `[x, v, y]`.
        have hnd₀ : [x, v, y].Nodup := by
          simp [hvx.ne.symm, hxy_ne, hvy.ne]
        have hsub₀ : ∀ w ∈ [x, v, y], w ∈ S := by
          intro w hw
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
          rcases hw with rfl | rfl | rfl <;> assumption
        have hchain₀ : IsAdjChain G [x, v, y] := ⟨hvx.symm, hvy, trivial⟩
        rcases extend_to_maximal_path S S.card [x, v, y] (List.cons_ne_nil _ _)
            (Nat.sub_le _ _) hnd₀ hsub₀ hchain₀ with
          ⟨P, hne, hpref, hnd, hsub, hchain, hmax⟩
        by_cases hfull : P.toFinset = S
        · exact color_case1_hamiltonian hk hdeg hpref hnd hfull hchain hvx hvy hnxy (hreg v hvS)
        · have hP_sub : P.toFinset ⊆ S := fun z hz => hsub z (List.mem_toFinset.mp hz)
          have hP_ssub : P.toFinset ⊂ S := ssubset_of_subset_of_ne hP_sub hfull
          have hP_lt : P.toFinset.card ≤ n := by
            have hlt := Finset.card_lt_card hP_ssub
            omega
          have hlast_mem : P.getLast hne ∈ S := hsub _ (List.getLast_mem hne)
          exact color_case2_cycle hk hdeg ih hScard hne hnd hsub hchain hmax
            (hreg _ hlast_mem) hP_lt

/-- **Brooks' theorem** (via Zając's short path-coloring proof): any finite simple graph of maximum
degree at most `k` (`k ≥ 3`) that is `(k + 1)`-clique-free is `k`-colorable. -/
theorem solution
    {V : Type u} [Fintype V] (G : SimpleGraph V) {k : ℕ} (hk : 3 ≤ k)
    (hdeg : ∀ v : V, (G.neighborSet v).encard ≤ k)
    (hnoK : G.CliqueFree (k + 1)) :
    G.Colorable k := by
  classical
  have hdeg_fin : ∀ v : V, (G.neighborFinset v).card ≤ k :=
    card_neighborFinset_le_of_encard_le hdeg
  rcases brooks_properOn G hk hdeg_fin hnoK (Finset.univ : Finset V).card Finset.univ le_rfl with
    ⟨c, hc⟩
  exact ⟨SimpleGraph.Coloring.mk c fun {u v} huv =>
    hc u (Finset.mem_univ u) v (Finset.mem_univ v) huv⟩

