-- Prove2me | solution 1 for Balinski61.Whitney.whitney_theorem
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T13:03:02.835325+00:00
-- url     : https://prove2.me/submissions/8b15b4f1-e7fb-42e8-a8eb-e301e74d71ec

/-
Whitney's theorem (Balinski 1961, p. 434): a finite graph with at least n+1 vertices is
"n-tuply connected" (stays connected after deleting fewer than n vertices) iff any two distinct
vertices are joined by n internally disjoint paths.

The hard direction is Menger's theorem, proved here in its set form (`SPGTLib.Menger.menger_set`)
by induction on |S| + number of adjacent pairs, following Diestel, Graph Theory, Theorem 3.3.1.
-/
import Mathlib
import Definitions.Def_Balinski61_Whitney_Graph

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace SPGTLib.Menger

variable {V : Type*} [DecidableEq V]

/-- A path of `G` inside the vertex set `S`, listed from a vertex of `A` to a vertex of `B`. -/
def IsABPath (G : SimpleGraph V) (S A B : Finset V) (p : List V) : Prop :=
  p ≠ [] ∧ p.Nodup ∧ List.IsChain G.Adj p ∧ (∀ v ∈ p, v ∈ S) ∧
    (∃ a, p.head? = some a ∧ a ∈ A) ∧ (∃ b, p.getLast? = some b ∧ b ∈ B)

/-- `X` meets every `A`–`B` path of `G` inside `S`. -/
def IsABSep (G : SimpleGraph V) (S A B X : Finset V) : Prop :=
  ∀ p, IsABPath G S A B p → ∃ x ∈ X, x ∈ p

/-- `k` pairwise vertex-disjoint `A`–`B` paths of `G` inside `S`. -/
def HasLinkage (G : SimpleGraph V) (S A B : Finset V) (k : ℕ) : Prop :=
  ∃ L : List (List V), L.length = k ∧ (∀ p ∈ L, IsABPath G S A B p) ∧
    L.Pairwise (fun p q => ∀ v ∈ p, v ∉ q)

section basics

variable {G G' : SimpleGraph V} {S S' A A' B B' X : Finset V} {p : List V}

theorem IsABPath.mono_graph (h : IsABPath G S A B p) (hG : G ≤ G') : IsABPath G' S A B p :=
  ⟨h.1, h.2.1, h.2.2.1.imp (fun _ _ hab => hG hab), h.2.2.2.1, h.2.2.2.2⟩

theorem IsABPath.mono (h : IsABPath G S A B p) (hS : S ⊆ S') (hA : A ⊆ A') (hB : B ⊆ B') :
    IsABPath G S' A' B' p := by
  obtain ⟨hne, hnd, hch, hSp, ⟨a, ha, haA⟩, ⟨b, hb, hbB⟩⟩ := h
  exact ⟨hne, hnd, hch, fun v hv => hS (hSp v hv), ⟨a, ha, hA haA⟩, ⟨b, hb, hB hbB⟩⟩

theorem IsABPath.reverse (h : IsABPath G S A B p) : IsABPath G S B A p.reverse := by
  obtain ⟨hne, hnd, hch, hSp, ⟨a, ha, haA⟩, ⟨b, hb, hbB⟩⟩ := h
  refine ⟨by simpa using hne, List.nodup_reverse.mpr hnd, ?_,
    fun v hv => hSp v (List.mem_reverse.mp hv),
    ⟨b, by simpa [List.head?_reverse] using hb, hbB⟩,
    ⟨a, by simpa [List.getLast?_reverse] using ha, haA⟩⟩
  rw [List.isChain_reverse]
  exact hch.imp (fun u w h => h.symm)

theorem IsABSep.symm (h : IsABSep G S A B X) : IsABSep G S B A X := by
  intro p hp
  obtain ⟨x, hx, hxp⟩ := h p.reverse hp.reverse
  exact ⟨x, hx, List.mem_reverse.mp hxp⟩

end basics

/-- Two members of a pairwise-disjoint family that share a vertex coincide. -/
theorem eq_of_mem_of_mem {L : List (List V)} (hL : L.Pairwise (fun p q => ∀ v ∈ p, v ∉ q))
    {p q : List V} (hp : p ∈ L) (hq : q ∈ L) {v : V} (hvp : v ∈ p) (hvq : v ∈ q) : p = q := by
  induction L with
  | nil => exact absurd hp (by simp)
  | cons a t ih =>
    rw [List.pairwise_cons] at hL
    obtain ⟨h1, h2⟩ := hL
    rcases List.mem_cons.mp hp with rfl | hpt <;> rcases List.mem_cons.mp hq with rfl | hqt
    · rfl
    · exact absurd hvq (h1 q hqt v hvp)
    · exact absurd hvp (h1 p hpt v hvq)
    · exact ih h2 hpt hqt

/-- A full-size family of disjoint paths ending in `X` ends in every vertex of `X` exactly once,
and meets `X` only at its last vertices. -/
theorem linkage_ends {G : SimpleGraph V} {S A X : Finset V} (L : List (List V))
    (hlen : L.length = X.card) (hL : ∀ p ∈ L, IsABPath G S A X p)
    (hpw : L.Pairwise (fun p q => ∀ v ∈ p, v ∉ q)) :
    (∀ x ∈ X, ∃ p ∈ L, p.getLast? = some x) ∧
      (∀ p ∈ L, ∀ v ∈ p, v ∈ X → p.getLast? = some v) := by
  by_cases hX : X = ∅
  · subst hX
    have : L = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
    subst this
    simp
  obtain ⟨x0, hx0⟩ := Finset.nonempty_iff_ne_empty.mpr hX
  let f : List V → V := fun p => (p.getLast?).getD x0
  have hf : ∀ p ∈ L, p.getLast? = some (f p) ∧ f p ∈ X := by
    intro p hp
    obtain ⟨b, hb, hbX⟩ := (hL p hp).2.2.2.2.2
    simp [f, hb, hbX]
  have hfmem : ∀ p ∈ L, f p ∈ p := fun p hp => List.mem_of_getLast? (hf p hp).1
  have hnd : (L.map f).Nodup := by
    rw [List.Nodup, List.pairwise_map]
    refine hpw.imp_of_mem ?_
    intro p q hp hq hdisj heq
    exact hdisj (f p) (hfmem p hp) (heq ▸ hfmem q hq)
  have hsub : (L.map f).toFinset ⊆ X := by
    intro v hv
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hv)
    exact (hf p hp).2
  have hcard : (L.map f).toFinset.card = X.card := by
    rw [List.toFinset_card_of_nodup hnd, List.length_map, hlen]
  have heq : (L.map f).toFinset = X := Finset.eq_of_subset_of_card_le hsub (by omega)
  refine ⟨fun x hx => ?_, fun p hp v hvp hvX => ?_⟩
  · rw [← heq] at hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hx)
    exact ⟨p, hp, (hf p hp).1⟩
  · rw [← heq] at hvX
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hvX)
    have hpq := eq_of_mem_of_mem hpw hp hq hvp (hfmem q hq)
    subst hpq
    exact (hf p hp).1

/-- Gluing an `A`–`X` linkage and a `B`–`X` linkage that meet only in `X`. -/
theorem combine {G : SimpleGraph V} {S SA SB A B X : Finset V}
    (hSA : SA ⊆ S) (hSB : SB ⊆ S) (hint : ∀ v, v ∈ SA → v ∈ SB → v ∈ X)
    (LA : List (List V)) (hLAlen : LA.length = X.card)
    (hLA : ∀ p ∈ LA, IsABPath G SA A X p) (hLApw : LA.Pairwise (fun p q => ∀ v ∈ p, v ∉ q))
    (LB : List (List V)) (hLBlen : LB.length = X.card)
    (hLB : ∀ p ∈ LB, IsABPath G SB B X p) (hLBpw : LB.Pairwise (fun p q => ∀ v ∈ p, v ∉ q)) :
    HasLinkage G S A B X.card := by
  obtain ⟨hA1, hA2⟩ := linkage_ends LA hLAlen hLA hLApw
  obtain ⟨hB1, hB2⟩ := linkage_ends LB hLBlen hLB hLBpw
  choose! pA hpA using hA1
  choose! pB hpB using hB1
  have hrev : ∀ x ∈ X, ∃ r, (pB x).reverse = x :: r := by
    intro x hx
    obtain ⟨hmem, hlast⟩ := hpB x hx
    have hne : (pB x).reverse ≠ [] := by simpa using (hLB _ hmem).1
    have hhead : (pB x).reverse.head? = some x := by rw [List.head?_reverse]; exact hlast
    cases hh : (pB x).reverse with
    | nil => exact absurd hh hne
    | cons a t =>
      rw [hh] at hhead
      simp at hhead
      exact ⟨t, by rw [hhead]⟩
  choose! r hr using hrev
  have hfact : ∀ x ∈ X,
      IsABPath G SA A X (pA x) ∧ (pA x).getLast? = some x ∧ (∀ v ∈ pA x, v ∈ X → v = x) ∧
      (∀ v ∈ r x, v ∈ SB ∧ v ∉ X) ∧ List.IsChain G.Adj (x :: r x) ∧ (x :: r x).Nodup ∧
      (∃ b, (x :: r x).getLast? = some b ∧ b ∈ B) := by
    intro x hx
    obtain ⟨hmem, hlast⟩ := hpA x hx
    obtain ⟨hmemB, hlastB⟩ := hpB x hx
    have hpath := hLB _ hmemB
    have hrx := hr x hx
    refine ⟨hLA _ hmem, hlast, ?_, ?_, ?_, ?_, ?_⟩
    · intro v hv hvX
      have := hA2 _ hmem v hv hvX
      rw [hlast] at this
      exact (Option.some.inj this).symm
    · intro v hv
      have hvB : v ∈ pB x := List.mem_reverse.mp (by rw [hrx]; exact List.mem_cons_of_mem _ hv)
      refine ⟨hpath.2.2.2.1 v hvB, fun hvX => ?_⟩
      have := hB2 _ hmemB v hvB hvX
      rw [hlastB] at this
      have hvx : v = x := (Option.some.inj this).symm
      have hnd : (x :: r x).Nodup := by rw [← hrx]; exact List.nodup_reverse.mpr hpath.2.1
      rw [List.nodup_cons] at hnd
      exact hnd.1 (hvx ▸ hv)
    · rw [← hrx, List.isChain_reverse]
      exact hpath.2.2.1.imp (fun a b h => h.symm)
    · rw [← hrx]; exact List.nodup_reverse.mpr hpath.2.1
    · obtain ⟨b, hb, hbB⟩ := hpath.2.2.2.2.1
      exact ⟨b, by rw [← hrx, List.getLast?_reverse]; exact hb, hbB⟩
  refine ⟨X.toList.map (fun x => pA x ++ r x), by simp, ?_, ?_⟩
  · intro p hp
    obtain ⟨x, hxl, rfl⟩ := List.mem_map.mp hp
    have hx : x ∈ X := Finset.mem_toList.mp hxl
    obtain ⟨hpath, hlast, honly, hrest, hch, hnd, hbend⟩ := hfact x hx
    have hdisj : ∀ v ∈ pA x, v ∉ r x := by
      intro v hv hvr
      have hvA := hpath.2.2.2.1 v hv
      obtain ⟨hvB, hvX⟩ := hrest v hvr
      exact hvX (hint v hvA hvB)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro h; exact hpath.1 (List.append_eq_nil_iff.mp h).1
    · rw [List.nodup_append]
      exact ⟨hpath.2.1, (List.nodup_cons.mp hnd).2, fun a ha b hb hab => hdisj a ha (hab ▸ hb)⟩
    · rw [List.isChain_append]
      refine ⟨hpath.2.2.1, (List.isChain_cons.mp hch).2, ?_⟩
      intro u hu w hw
      rw [hlast] at hu
      have hux : x = u := Option.some.inj hu
      subst hux
      exact (List.isChain_cons.mp hch).1 w hw
    · intro v hv
      rcases List.mem_append.mp hv with h | h
      · exact hSA (hpath.2.2.2.1 v h)
      · exact hSB (hrest v h).1
    · obtain ⟨a, ha, haA⟩ := hpath.2.2.2.2.1
      refine ⟨a, ?_, haA⟩
      rw [List.head?_append_of_ne_nil _ hpath.1]; exact ha
    · obtain ⟨b, hb, hbB⟩ := hbend
      refine ⟨b, ?_, hbB⟩
      rcases hrr : r x with _ | ⟨y, t⟩
      · rw [hrr] at hb
        simp at hb
        subst hb
        simpa using hlast
      · rw [hrr] at hb
        rw [List.getLast?_append_of_ne_nil _ (by simp)]
        simpa [List.getLast?_cons] using hb
  · rw [List.pairwise_map]
    refine (show X.toList.Pairwise (· ≠ ·) from Finset.nodup_toList X).imp_of_mem ?_
    intro x y hxl hyl hxy v hvx hvy
    have hx : x ∈ X := Finset.mem_toList.mp hxl
    have hy : y ∈ X := Finset.mem_toList.mp hyl
    obtain ⟨hpathx, hlastx, honlyx, hrestx, _, _, _⟩ := hfact x hx
    obtain ⟨hpathy, hlasty, honlyy, hresty, _, _, _⟩ := hfact y hy
    rcases List.mem_append.mp hvx with h1 | h1 <;> rcases List.mem_append.mp hvy with h2 | h2
    · have := eq_of_mem_of_mem hLApw (hpA x hx).1 (hpA y hy).1 h1 h2
      rw [this] at hlastx
      rw [hlastx] at hlasty
      exact hxy (Option.some.inj hlasty)
    · exact (hresty v h2).2 (hint v (hpathx.2.2.2.1 v h1) (hresty v h2).1)
    · exact (hrestx v h1).2 (hint v (hpathy.2.2.2.1 v h2) (hrestx v h1).1)
    · have hv1 : v ∈ pB x := List.mem_reverse.mp (by rw [hr x hx]; exact List.mem_cons_of_mem _ h1)
      have hv2 : v ∈ pB y := List.mem_reverse.mp (by rw [hr y hy]; exact List.mem_cons_of_mem _ h2)
      have := eq_of_mem_of_mem hLBpw (hpB x hx).1 (hpB y hy).1 hv1 hv2
      have h3 := (hpB x hx).2
      have h4 := (hpB y hy).2
      rw [this] at h3
      rw [h3] at h4
      exact hxy (Option.some.inj h4)

/-- The subgraph of `G` induced on `T`, as a graph on the same vertex type. -/
def Hgraph (G : SimpleGraph V) (T : Finset V) : SimpleGraph V where
  Adj u w := G.Adj u w ∧ u ∈ T ∧ w ∈ T
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => G.loopless.irrefl _ h.1⟩

open Classical in
/-- Vertices of `T` reachable inside `T` from a vertex of `A ∩ T`. -/
noncomputable def reachSet (G : SimpleGraph V) (T A : Finset V) : Finset V :=
  T.filter (fun v => ∃ a ∈ A, a ∈ T ∧ (Hgraph G T).Reachable a v)

theorem mem_reachSet {G : SimpleGraph V} {T A : Finset V} {v : V} :
    v ∈ reachSet G T A ↔ v ∈ T ∧ ∃ a ∈ A, a ∈ T ∧ (Hgraph G T).Reachable a v := by
  unfold reachSet
  simp

theorem walk_support_mem {G : SimpleGraph V} {T : Finset V} {a b : V}
    (w : (Hgraph G T).Walk a b) (ha : a ∈ T) : ∀ v ∈ w.support, v ∈ T := by
  induction w with
  | nil => intro v hv; simp at hv; exact hv ▸ ha
  | cons h w ih =>
    intro v hv
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hv
    rcases hv with rfl | hv
    · exact ha
    · exact ih h.2.2 v hv

theorem reach_mem {G : SimpleGraph V} {T : Finset V} {a b : V}
    (h : (Hgraph G T).Reachable a b) (ha : a ∈ T) : b ∈ T := by
  obtain ⟨w⟩ := h
  exact walk_support_mem w ha b w.end_mem_support

theorem reach_of_chain {G : SimpleGraph V} {T : Finset V} :
    ∀ (p : List V) (a : V), p.head? = some a → List.IsChain G.Adj p → (∀ v ∈ p, v ∈ T) →
      ∀ v ∈ p, (Hgraph G T).Reachable a v := by
  intro p
  induction p with
  | nil => intro a h; simp at h
  | cons b t ih =>
    intro a ha hch hT v hv
    have hab : b = a := by simpa using ha
    subst hab
    rcases List.mem_cons.mp hv with rfl | hvt
    · exact SimpleGraph.Reachable.refl _
    · cases t with
      | nil => exact absurd hvt (by simp)
      | cons c t' =>
        have hadj : G.Adj b c := (List.isChain_cons_cons.mp hch).1
        have hH : (Hgraph G T).Adj b c := ⟨hadj, hT b (by simp), hT c (by simp)⟩
        have := ih c rfl (List.isChain_cons_cons.mp hch).2
          (fun w hw => hT w (List.mem_cons_of_mem _ hw)) v hvt
        exact hH.reachable.trans this

theorem exists_path_of_reach {G : SimpleGraph V} {T : Finset V} {a b : V} (ha : a ∈ T)
    (h : (Hgraph G T).Reachable a b) : ∃ p, IsABPath G T {a} {b} p := by
  obtain ⟨w⟩ := h
  let P := w.toPath
  refine ⟨P.1.support, P.1.support_ne_nil, P.2.support_nodup, ?_, ?_, ⟨a, ?_, by simp⟩,
    ⟨b, ?_, by simp⟩⟩
  · exact P.1.isChain_adj_support.imp (fun u v huv => huv.1)
  · exact walk_support_mem P.1 ha
  · rw [← SimpleGraph.Walk.cons_tail_support P.1]; rfl
  · rw [List.getLast?_eq_some_getLast (SimpleGraph.Walk.support_ne_nil P.1),
      SimpleGraph.Walk.getLast_support]

theorem firstX_prefix {G : SimpleGraph V} {S X : Finset V} (a0 : V) :
    ∀ (p : List V) (c : V), p.head? = some c → List.IsChain G.Adj p → (∀ v ∈ p, v ∈ S) →
      (c ∈ X ∨ (a0 ∈ S \ X ∧ (Hgraph G (S \ X)).Reachable a0 c)) → (∃ x ∈ X, x ∈ p) →
      ∃ q, q <+: p ∧ q.head? = some c ∧ (∃ x ∈ X, q.getLast? = some x) ∧
        ∀ v ∈ q, v ∈ X ∨ (a0 ∈ S \ X ∧ (Hgraph G (S \ X)).Reachable a0 v) := by
  intro p
  induction p with
  | nil => intro c h; simp at h
  | cons b t ih =>
    intro c hc hch hS hcase ⟨x, hxX, hxp⟩
    have hbc : b = c := by simpa using hc
    subst hbc
    by_cases hbX : b ∈ X
    · refine ⟨[b], ⟨t, rfl⟩, rfl, ⟨b, hbX, rfl⟩, ?_⟩
      intro v hv
      simp at hv
      exact Or.inl (hv ▸ hbX)
    · have hcase' : a0 ∈ S \ X ∧ (Hgraph G (S \ X)).Reachable a0 b := by
        rcases hcase with h | h
        · exact absurd h hbX
        · exact h
      have hxt : x ∈ t := by
        rcases List.mem_cons.mp hxp with rfl | h
        · exact absurd hxX hbX
        · exact h
      cases t with
      | nil => exact absurd hxt (by simp)
      | cons d t' =>
        have hadj : G.Adj b d := (List.isChain_cons_cons.mp hch).1
        have hbS : b ∈ S \ X := Finset.mem_sdiff.mpr ⟨hS b (by simp), hbX⟩
        have hdS : d ∈ S := hS d (by simp)
        have hdcase : d ∈ X ∨ (a0 ∈ S \ X ∧ (Hgraph G (S \ X)).Reachable a0 d) := by
          by_cases hdX : d ∈ X
          · exact Or.inl hdX
          · exact Or.inr ⟨hcase'.1, hcase'.2.trans
              (SimpleGraph.Adj.reachable (show (Hgraph G (S \ X)).Adj b d from
                ⟨hadj, hbS, Finset.mem_sdiff.mpr ⟨hdS, hdX⟩⟩))⟩
        obtain ⟨q', hq'p, hq'h, ⟨x', hx'X, hx'⟩, hq'v⟩ := ih d rfl
          (List.isChain_cons_cons.mp hch).2 (fun w hw => hS w (List.mem_cons_of_mem _ hw))
          hdcase ⟨x, hxX, hxt⟩
        obtain ⟨u, hu⟩ := hq'p
        refine ⟨b :: q', ⟨u, by simp [hu]⟩, rfl, ⟨x', hx'X, ?_⟩, ?_⟩
        · cases q' with
          | nil => simp at hq'h
          | cons e q'' => simpa [List.getLast?_cons_cons] using hx'
        · intro v hv
          rcases List.mem_cons.mp hv with rfl | hv
          · exact Or.inr hcase'
          · exact hq'v v hv

/-- A separator of the `A`–`X` subproblem separates `A` from `B` in the whole graph. -/
theorem sep_restrict {G : SimpleGraph V} {S A B X X'' : Finset V} (hX : IsABSep G S A B X)
    (h'' : IsABSep G (reachSet G (S \ X) A ∪ X) A X X'') : IsABSep G S A B X'' := by
  intro p hp
  have hp' := hp
  obtain ⟨hne, hnd, hch, hSp, ⟨a0, ha0, ha0A⟩, ⟨b, hb, hbB⟩⟩ := hp'
  obtain ⟨x, hxX, hxp⟩ := hX p hp
  have ha0S : a0 ∈ S := hSp a0 (List.mem_of_mem_head? ha0)
  have hcase : a0 ∈ X ∨ (a0 ∈ S \ X ∧ (Hgraph G (S \ X)).Reachable a0 a0) := by
    by_cases h : a0 ∈ X
    · exact Or.inl h
    · exact Or.inr ⟨Finset.mem_sdiff.mpr ⟨ha0S, h⟩, SimpleGraph.Reachable.refl _⟩
  obtain ⟨q, hqp, hqh, ⟨x', hx'X, hx'⟩, hqv⟩ :=
    firstX_prefix a0 p a0 ha0 hch hSp hcase ⟨x, hxX, hxp⟩
  have hqpath : IsABPath G (reachSet G (S \ X) A ∪ X) A X q := by
    obtain ⟨u, hu⟩ := hqp
    refine ⟨?_, ?_, ?_, ?_, ⟨a0, hqh, ha0A⟩, ⟨x', hx', hx'X⟩⟩
    · intro h; subst h; simp at hqh
    · rw [← hu] at hnd; exact (List.nodup_append.mp hnd).1
    · rw [← hu] at hch; exact (List.isChain_append.mp hch).1
    · intro v hv
      rcases hqv v hv with h | ⟨ha0T, hr⟩
      · exact Finset.mem_union_right _ h
      · exact Finset.mem_union_left _ (mem_reachSet.mpr
          ⟨reach_mem hr ha0T, a0, ha0A, ha0T, hr⟩)
  obtain ⟨y, hy, hyq⟩ := h'' q hqpath
  exact ⟨y, hy, hqp.subset hyq⟩

open Classical in
/-- Number of ordered adjacent pairs inside `S` (the measure for the induction). -/
noncomputable def edgeCount (G : SimpleGraph V) (S : Finset V) : ℕ :=
  ((S ×ˢ S).filter (fun x => G.Adj x.1 x.2)).card

theorem edgeCount_mono {G : SimpleGraph V} {S S' : Finset V} (h : S ⊆ S') :
    edgeCount G S ≤ edgeCount G S' := by
  classical
  unfold edgeCount
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_product] at hx ⊢
  exact ⟨⟨h hx.1.1, h hx.1.2⟩, hx.2⟩

theorem edgeCount_delete_lt {G : SimpleGraph V} {S : Finset V} {u w : V} (hadj : G.Adj u w)
    (hu : u ∈ S) (hw : w ∈ S) : edgeCount (G.deleteEdges {s(u, w)}) S < edgeCount G S := by
  classical
  unfold edgeCount
  apply Finset.card_lt_card
  refine ⟨?_, ?_⟩
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_product, SimpleGraph.deleteEdges_adj] at hx ⊢
    exact ⟨hx.1, hx.2.1⟩
  · intro hsub
    have := hsub (show (u, w) ∈ (S ×ˢ S).filter (fun x => G.Adj x.1 x.2) by
      simp only [Finset.mem_filter, Finset.mem_product]; exact ⟨⟨hu, hw⟩, hadj⟩)
    simp only [Finset.mem_filter, Finset.mem_product, SimpleGraph.deleteEdges_adj] at this
    exact this.2.2 (by simp)

theorem chain_delete {G : SimpleGraph V} {u w : V} :
    ∀ q : List V, List.IsChain G.Adj q → ¬ (u ∈ q ∧ w ∈ q) →
      List.IsChain (G.deleteEdges {s(u, w)}).Adj q := by
  intro q
  induction q with
  | nil => intro _ _; exact List.isChain_nil
  | cons a t ih =>
    intro hch hnot
    cases t with
    | nil => exact List.isChain_singleton _
    | cons b t' =>
      obtain ⟨hab, hrest⟩ := List.isChain_cons_cons.mp hch
      refine List.isChain_cons_cons.mpr ⟨?_, ih hrest (fun h => hnot ⟨List.mem_cons_of_mem _ h.1, List.mem_cons_of_mem _ h.2⟩)⟩
      rw [SimpleGraph.deleteEdges_adj]
      refine ⟨hab, ?_⟩
      intro hmem
      rw [Set.mem_singleton_iff, Sym2.eq_iff] at hmem
      apply hnot
      rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨by simp, by simp⟩
      · exact ⟨by simp, by simp⟩

theorem no_AB_path_in_T {G : SimpleGraph V} {S A B X : Finset V} (hX : IsABSep G S A B X)
    (hXS : X ⊆ S) {a b : V} (ha : a ∈ A) (hb : b ∈ B) (haT : a ∈ S \ X)
    (hr : (Hgraph G (S \ X)).Reachable a b) : False := by
  obtain ⟨p, hp⟩ := exists_path_of_reach haT hr
  have hp' : IsABPath G S A B p := hp.mono Finset.sdiff_subset (by simpa using ha) (by simpa using hb)
  obtain ⟨x, hxX, hxp⟩ := hX p hp'
  have hxT : x ∈ S \ X := hp.2.2.2.1 x hxp
  exact (Finset.mem_sdiff.mp hxT).2 hxX

theorem sep_of_whole {G : SimpleGraph V} {S A B : Finset V} : IsABSep G S A B B := by
  intro p hp
  obtain ⟨b, hb, hbB⟩ := hp.2.2.2.2.2
  exact ⟨b, hbB, List.mem_of_getLast? hb⟩

theorem sep_of_whole' {G : SimpleGraph V} {S A B : Finset V} : IsABSep G S A B A := by
  intro p hp
  obtain ⟨a, ha, haA⟩ := hp.2.2.2.2.1
  exact ⟨a, haA, List.mem_of_mem_head? ha⟩

/-- The splitting case of Menger's theorem: a minimum separator `X` different from `A` and `B`. -/
theorem case_split (G : SimpleGraph V) (S A B X : Finset V) (k n : ℕ)
    (hμ : S.card + edgeCount G S ≤ n + 1) (hA : A ⊆ S) (hB : B ⊆ S)
    (hsep : ∀ X, X ⊆ S → IsABSep G S A B X → k ≤ X.card)
    (hXS : X ⊆ S) (hXsep : IsABSep G S A B X) (hXk : X.card = k) (hXA : X ≠ A) (hXB : X ≠ B)
    (ih : ∀ (G : SimpleGraph V) (S A B : Finset V) (k : ℕ),
      S.card + edgeCount G S ≤ n → A ⊆ S → B ⊆ S →
      (∀ X, X ⊆ S → IsABSep G S A B X → k ≤ X.card) → HasLinkage G S A B k) :
    HasLinkage G S A B k := by
  classical
  have hBnX : ¬ B ⊆ X := by
    intro hBX
    have h1 := hsep B hB sep_of_whole
    exact hXB (Finset.eq_of_subset_of_card_le hBX (by omega)).symm
  have hAnX : ¬ A ⊆ X := by
    intro hAX
    have h1 := hsep A hA sep_of_whole'
    exact hXA (Finset.eq_of_subset_of_card_le hAX (by omega)).symm
  obtain ⟨b, hbB, hbX⟩ := Finset.not_subset.mp hBnX
  obtain ⟨a, haA, haX⟩ := Finset.not_subset.mp hAnX
  set T := S \ X with hT
  set VA := reachSet G T A with hVA
  set VB := reachSet G T B with hVB
  set SA := VA ∪ X with hSAdef
  set SB := VB ∪ X with hSBdef
  have hVAT : VA ⊆ T := fun v hv => (mem_reachSet.mp hv).1
  have hVBT : VB ⊆ T := fun v hv => (mem_reachSet.mp hv).1
  have hSAS : SA ⊆ S := Finset.union_subset (hVAT.trans Finset.sdiff_subset) hXS
  have hSBS : SB ⊆ S := Finset.union_subset (hVBT.trans Finset.sdiff_subset) hXS
  have hASA : A ⊆ SA := by
    intro v hv
    by_cases hvX : v ∈ X
    · exact Finset.mem_union_right _ hvX
    · exact Finset.mem_union_left _ (mem_reachSet.mpr ⟨Finset.mem_sdiff.mpr ⟨hA hv, hvX⟩, v, hv,
        Finset.mem_sdiff.mpr ⟨hA hv, hvX⟩, SimpleGraph.Reachable.refl _⟩)
  have hBSB : B ⊆ SB := by
    intro v hv
    by_cases hvX : v ∈ X
    · exact Finset.mem_union_right _ hvX
    · exact Finset.mem_union_left _ (mem_reachSet.mpr ⟨Finset.mem_sdiff.mpr ⟨hB hv, hvX⟩, v, hv,
        Finset.mem_sdiff.mpr ⟨hB hv, hvX⟩, SimpleGraph.Reachable.refl _⟩)
  have hXSA : X ⊆ SA := Finset.subset_union_right
  have hXSB : X ⊆ SB := Finset.subset_union_right
  have hbT : b ∈ T := Finset.mem_sdiff.mpr ⟨hB hbB, hbX⟩
  have haT : a ∈ T := Finset.mem_sdiff.mpr ⟨hA haA, haX⟩
  have hbSA : b ∉ SA := by
    intro hb
    rcases Finset.mem_union.mp hb with hb | hb
    · obtain ⟨_, a', ha', ha'T, hr⟩ := mem_reachSet.mp hb
      exact no_AB_path_in_T hXsep hXS ha' hbB ha'T hr
    · exact hbX hb
  have haSB : a ∉ SB := by
    intro ha
    rcases Finset.mem_union.mp ha with ha | ha
    · obtain ⟨_, b', hb', hb'T, hr⟩ := mem_reachSet.mp ha
      exact no_AB_path_in_T hXsep hXS haA hb' haT hr.symm
    · exact haX ha
  have hVAVB : ∀ v, v ∈ VA → v ∈ VB → False := by
    intro v hvA hvB
    obtain ⟨_, a', ha', ha'T, hra⟩ := mem_reachSet.mp hvA
    obtain ⟨_, b', hb', hb'T, hrb⟩ := mem_reachSet.mp hvB
    exact no_AB_path_in_T hXsep hXS ha' hb' ha'T (hra.trans hrb.symm)
  have hint : ∀ v, v ∈ SA → v ∈ SB → v ∈ X := by
    intro v hvA hvB
    rcases Finset.mem_union.mp hvA with h1 | h1
    · rcases Finset.mem_union.mp hvB with h2 | h2
      · exact absurd (hVAVB v h1 h2) id
      · exact h2
    · exact h1
  have hSAlt : SA.card < S.card := Finset.card_lt_card ⟨hSAS, fun h => hbSA (h (hB hbB))⟩
  have hSBlt : SB.card < S.card := Finset.card_lt_card ⟨hSBS, fun h => haSB (h (hA haA))⟩
  have hμA : SA.card + edgeCount G SA ≤ n := by
    have := edgeCount_mono (G := G) hSAS
    omega
  have hμB : SB.card + edgeCount G SB ≤ n := by
    have := edgeCount_mono (G := G) hSBS
    omega
  have hsepA : ∀ X'', X'' ⊆ SA → IsABSep G SA A X X'' → k ≤ X''.card :=
    fun X'' hX'' hsp => hsep X'' (hX''.trans hSAS) (sep_restrict hXsep hsp)
  have hsepB : ∀ X'', X'' ⊆ SB → IsABSep G SB B X X'' → k ≤ X''.card :=
    fun X'' hX'' hsp => hsep X'' (hX''.trans hSBS) (sep_restrict hXsep.symm hsp).symm
  obtain ⟨LA, hLAlen, hLA, hLApw⟩ := ih G SA A X k hμA hASA hXSA hsepA
  obtain ⟨LB, hLBlen, hLB, hLBpw⟩ := ih G SB B X k hμB hBSB hXSB hsepB
  have := combine hSAS hSBS hint LA (by omega) hLA hLApw LB (by omega) hLB hLBpw
  rwa [hXk] at this

/-- A vertex lying in `A ∩ B` is a trivial path; remove it and induct. -/
theorem case_common (G : SimpleGraph V) (S A B : Finset V) (k n : ℕ)
    (hμ : S.card + edgeCount G S ≤ n + 1) (hA : A ⊆ S) (hB : B ⊆ S)
    (hsep : ∀ X, X ⊆ S → IsABSep G S A B X → k ≤ X.card) (x : V) (hxA : x ∈ A) (hxB : x ∈ B)
    (ih : ∀ (G : SimpleGraph V) (S A B : Finset V) (k : ℕ),
      S.card + edgeCount G S ≤ n → A ⊆ S → B ⊆ S →
      (∀ X, X ⊆ S → IsABSep G S A B X → k ≤ X.card) → HasLinkage G S A B k) :
    HasLinkage G S A B k := by
  classical
  have hxS : x ∈ S := hA hxA
  by_cases hk : k = 0
  · subst hk; exact ⟨[], rfl, by simp, List.Pairwise.nil⟩
  have hcard : (S.erase x).card + 1 = S.card := Finset.card_erase_add_one hxS
  have hμ' : (S.erase x).card + edgeCount G (S.erase x) ≤ n := by
    have := edgeCount_mono (G := G) (Finset.erase_subset x S)
    omega
  have hsep' : ∀ X', X' ⊆ S.erase x → IsABSep G (S.erase x) (A.erase x) (B.erase x) X' →
      k - 1 ≤ X'.card := by
    intro X' hX'S hsp
    have hsp2 : IsABSep G S A B (insert x X') := by
      intro q hq
      by_cases hxq : x ∈ q
      · exact ⟨x, Finset.mem_insert_self _ _, hxq⟩
      · obtain ⟨hne, hnd, hch, hSq, ⟨a, ha, haA⟩, ⟨b, hb, hbB⟩⟩ := hq
        have hq' : IsABPath G (S.erase x) (A.erase x) (B.erase x) q := by
          refine ⟨hne, hnd, hch, ?_, ⟨a, ha, ?_⟩, ⟨b, hb, ?_⟩⟩
          · intro v hv
            exact Finset.mem_erase.mpr ⟨fun h => hxq (h ▸ hv), hSq v hv⟩
          · exact Finset.mem_erase.mpr ⟨fun h => hxq (h ▸ List.mem_of_mem_head? ha), haA⟩
          · exact Finset.mem_erase.mpr ⟨fun h => hxq (h ▸ List.mem_of_getLast? hb), hbB⟩
        obtain ⟨y, hy, hyq⟩ := hsp q hq'
        exact ⟨y, Finset.mem_insert_of_mem hy, hyq⟩
    have hsub : insert x X' ⊆ S :=
      Finset.insert_subset hxS (hX'S.trans (Finset.erase_subset x S))
    have h1 := hsep _ hsub hsp2
    have h2 := Finset.card_insert_le x X'
    omega
  obtain ⟨L, hL1, hL2, hL3⟩ := ih G (S.erase x) (A.erase x) (B.erase x) (k - 1) hμ'
    (Finset.erase_subset_erase x hA) (Finset.erase_subset_erase x hB) hsep'
  refine ⟨[x] :: L, by simp [hL1]; omega, ?_, ?_⟩
  · intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · refine ⟨by simp, by simp, List.isChain_singleton _, ?_, ⟨x, rfl, hxA⟩, ⟨x, rfl, hxB⟩⟩
      intro v hv
      simp at hv
      exact hv ▸ hxS
    · exact (hL2 q hq).mono (Finset.erase_subset _ _) (Finset.erase_subset _ _)
        (Finset.erase_subset _ _)
  · rw [List.pairwise_cons]
    refine ⟨fun q hq v hv hvq => ?_, hL3⟩
    simp at hv
    subst hv
    have := (hL2 q hq).2.2.2.1 v hvq
    exact (Finset.notMem_erase v S) this

/-- No common vertex and every minimum separator is `A` or `B`: delete an edge and induct. -/
theorem case_edge (G : SimpleGraph V) (S A B : Finset V) (k n : ℕ)
    (hμ : S.card + edgeCount G S ≤ n + 1) (hA : A ⊆ S) (hB : B ⊆ S)
    (hsep : ∀ X, X ⊆ S → IsABSep G S A B X → k ≤ X.card) (hk : k ≠ 0)
    (hX' : ∀ X, X ⊆ S → IsABSep G S A B X → X.card = k → X = A ∨ X = B)
    (hAB : ∀ x, x ∈ A → x ∈ B → False)
    (ih : ∀ (G : SimpleGraph V) (S A B : Finset V) (k : ℕ),
      S.card + edgeCount G S ≤ n → A ⊆ S → B ⊆ S →
      (∀ X, X ⊆ S → IsABSep G S A B X → k ≤ X.card) → HasLinkage G S A B k) :
    HasLinkage G S A B k := by
  classical
  have hex : ∃ p, IsABPath G S A B p := by
    by_contra hno
    push_neg at hno
    have hsp : IsABSep G S A B ∅ := fun p hp => absurd hp (hno p)
    have := hsep ∅ (Finset.empty_subset _) hsp
    simp at this
    exact hk this
  obtain ⟨p, hp⟩ := hex
  obtain ⟨p0, p1, rest, rfl⟩ : ∃ p0 p1 rest, p = p0 :: p1 :: rest := by
    rcases p with _ | ⟨p0, _ | ⟨p1, rest⟩⟩
    · exact absurd rfl hp.1
    · obtain ⟨a, ha, haA⟩ := hp.2.2.2.2.1
      obtain ⟨b, hb, hbB⟩ := hp.2.2.2.2.2
      simp at ha hb
      subst ha
      subst hb
      exact absurd haA (fun h => hAB _ h hbB)
    · exact ⟨p0, p1, rest, rfl⟩
  have hp0A : p0 ∈ A := by
    obtain ⟨a, ha, haA⟩ := hp.2.2.2.2.1
    simp at ha
    exact ha ▸ haA
  have hadj : G.Adj p0 p1 := (List.isChain_cons_cons.mp hp.2.2.1).1
  have hp0S : p0 ∈ S := hp.2.2.2.1 p0 (by simp)
  have hp1S : p1 ∈ S := hp.2.2.2.1 p1 (by simp)
  have hne01 : p0 ≠ p1 := hadj.ne
  have hμ' : S.card + edgeCount (G.deleteEdges {s(p0, p1)}) S ≤ n := by
    have := edgeCount_delete_lt hadj hp0S hp1S
    omega
  by_cases hG' : ∀ X, X ⊆ S → IsABSep (G.deleteEdges {s(p0, p1)}) S A B X → k ≤ X.card
  · obtain ⟨L, h1, h2, h3⟩ := ih (G.deleteEdges {s(p0, p1)}) S A B k hμ' hA hB hG'
    exact ⟨L, h1, fun q hq => (h2 q hq).mono_graph (SimpleGraph.deleteEdges_le _), h3⟩
  · push_neg at hG'
    obtain ⟨X', hX'S, hX'sep, hX'k⟩ := hG'
    have hins : ∀ y, (y = p0 ∨ y = p1) → IsABSep G S A B (insert y X') := by
      intro y hy q hq
      by_cases hboth : p0 ∈ q ∧ p1 ∈ q
      · refine ⟨y, Finset.mem_insert_self _ _, ?_⟩
        rcases hy with rfl | rfl
        · exact hboth.1
        · exact hboth.2
      · have hq' : IsABPath (G.deleteEdges {s(p0, p1)}) S A B q :=
          ⟨hq.1, hq.2.1, chain_delete q hq.2.2.1 hboth, hq.2.2.2.1, hq.2.2.2.2⟩
        obtain ⟨x, hx, hxq⟩ := hX'sep q hq'
        exact ⟨x, Finset.mem_insert_of_mem hx, hxq⟩
    have hsub : ∀ y, y ∈ S → insert y X' ⊆ S := fun y hy => Finset.insert_subset hy hX'S
    have hcard : ∀ y, (y = p0 ∨ y = p1) → y ∈ S → y ∉ X' ∧ (insert y X').card = k := by
      intro y hy hyS
      have h1 := hsep _ (hsub y hyS) (hins y hy)
      by_cases hyX : y ∈ X'
      · rw [Finset.insert_eq_of_mem hyX] at h1
        omega
      · refine ⟨hyX, ?_⟩
        rw [Finset.card_insert_of_notMem hyX] at h1 ⊢
        omega
    obtain ⟨hp0X, hc0⟩ := hcard p0 (Or.inl rfl) hp0S
    obtain ⟨hp1X, hc1⟩ := hcard p1 (Or.inr rfl) hp1S
    have h0 := hX' _ (hsub p0 hp0S) (hins p0 (Or.inl rfl)) hc0
    have h1 := hX' _ (hsub p1 hp1S) (hins p1 (Or.inr rfl)) hc1
    have hX1A : insert p0 X' = A := by
      rcases h0 with h | h
      · exact h
      · exact absurd (h ▸ Finset.mem_insert_self _ _) (fun hb => hAB p0 hp0A hb)
    have hX2B : insert p1 X' = B := by
      rcases h1 with h | h
      · exfalso
        have : p0 ∈ insert p1 X' := by rw [h, ← hX1A]; exact Finset.mem_insert_self _ _
        rcases Finset.mem_insert.mp this with h' | h'
        · exact hne01 h'
        · exact hp0X h'
      · exact h
    have hX'empty : X' = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro x hx
      exact hAB x (hX1A ▸ Finset.mem_insert_of_mem hx) (hX2B ▸ Finset.mem_insert_of_mem hx)
    have hk1 : k = 1 := by
      rw [hX'empty] at hc0
      simpa using hc0.symm
    refine ⟨[[p0, p1]], by simp [hk1], ?_, by simp⟩
    intro q hq
    rw [List.mem_singleton] at hq
    subst hq
    refine ⟨by simp, by simp [hne01], List.isChain_pair.mpr hadj, ?_, ⟨p0, rfl, hp0A⟩,
      ⟨p1, rfl, hX2B ▸ Finset.mem_insert_self _ _⟩⟩
    intro v hv
    simp at hv
    rcases hv with rfl | rfl
    · exact hp0S
    · exact hp1S

theorem menger_aux : ∀ (n : ℕ) (G : SimpleGraph V) (S A B : Finset V) (k : ℕ),
    S.card + edgeCount G S ≤ n → A ⊆ S → B ⊆ S →
    (∀ X, X ⊆ S → IsABSep G S A B X → k ≤ X.card) → HasLinkage G S A B k := by
  intro n
  induction n with
  | zero =>
    intro G S A B k hμ hA hB hsep
    have hS : S = ∅ := Finset.card_eq_zero.mp (by omega)
    subst hS
    have hsp : IsABSep G ∅ A B ∅ := by
      intro p hp
      exfalso
      obtain ⟨hne, -, -, hS, -⟩ := hp
      obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil p hne
      simpa using hS v hv
    have := hsep ∅ (Finset.Subset.refl _) hsp
    have hk : k = 0 := by simpa using this
    subst hk
    exact ⟨[], rfl, by simp, List.Pairwise.nil⟩
  | succ n ih =>
    intro G S A B k hμ hA hB hsep
    by_cases hk : k = 0
    · subst hk; exact ⟨[], rfl, by simp, List.Pairwise.nil⟩
    by_cases hX : ∃ X, X ⊆ S ∧ IsABSep G S A B X ∧ X.card = k ∧ X ≠ A ∧ X ≠ B
    · obtain ⟨X, hXS, hXsep, hXk, hXA, hXB⟩ := hX
      exact case_split G S A B X k n hμ hA hB hsep hXS hXsep hXk hXA hXB ih
    · have hX' : ∀ X, X ⊆ S → IsABSep G S A B X → X.card = k → X = A ∨ X = B := by
        intro X hXS hXsep hXk
        by_contra hcon
        push_neg at hcon
        exact hX ⟨X, hXS, hXsep, hXk, hcon.1, hcon.2⟩
      by_cases hAB : ∃ x, x ∈ A ∧ x ∈ B
      · obtain ⟨x, hxA, hxB⟩ := hAB
        exact case_common G S A B k n hμ hA hB hsep x hxA hxB ih
      · exact case_edge G S A B k n hμ hA hB hsep hk hX'
          (fun x hxA hxB => hAB ⟨x, hxA, hxB⟩) ih

/-- Menger's theorem, set version (Diestel 3.3.1): if every `A`–`B` separator has at least `k`
vertices then there are `k` disjoint `A`–`B` paths. -/
theorem menger_set (G : SimpleGraph V) (S A B : Finset V) (hA : A ⊆ S) (hB : B ⊆ S) (k : ℕ)
    (hsep : ∀ X, X ⊆ S → IsABSep G S A B X → k ≤ X.card) : HasLinkage G S A B k :=
  menger_aux (S.card + edgeCount G S) G S A B k le_rfl hA hB hsep

end SPGTLib.Menger

namespace SPGTLib.Whitney

open Balinski61.Whitney SPGTLib.Menger

variable {V : Type*}

/-- A predicate closed under the steps of `H` propagates along walks. -/
theorem walk_closed {W : Type*} {H : SimpleGraph W} (Q : W → Prop)
    (hQ : ∀ u w, H.Adj u w → Q u → Q w) : ∀ {a b : W} (_p : H.Walk a b), Q a → Q b := by
  intro a b p
  induction p with
  | nil => exact id
  | cons h _ ih => intro ha; exact ih (hQ _ _ h ha)

/-- Reachability in an induced subgraph gives a walk of `G` inside the set. -/
theorem walk_avoid (G : SimpleGraph V) (Y : Set V) {a b : V} (ha : a ∈ Y) (hb : b ∈ Y)
    (h : (G.induce Y).Reachable ⟨a, ha⟩ ⟨b, hb⟩) :
    ∃ p : G.Walk a b, ∀ x ∈ p.support, x ∈ Y := by
  obtain ⟨w⟩ := h
  have key : ∀ {x y : ↥Y} (w : (G.induce Y).Walk x y),
      ∀ z ∈ (w.map (SimpleGraph.Embedding.induce Y).toHom).support, z ∈ Y := by
    intro x y w z hz
    rw [SimpleGraph.Walk.support_map] at hz
    obtain ⟨y, _, rfl⟩ := List.mem_map.mp hz
    exact y.2
  exact ⟨w.map (SimpleGraph.Embedding.induce Y).toHom, key w⟩

/-- A path from `s` to `t` all of whose vertices lie in `{s, t}` has support `[s, t]`. -/
theorem support_eq_pair {G : SimpleGraph V} {s t : V} (p : G.Walk s t) (hp : p.IsPath)
    (hst : s ≠ t) (hsub : ∀ x ∈ p.support, x = s ∨ x = t) : p.support = [s, t] := by
  have hc := SimpleGraph.Walk.cons_tail_support p
  have hnd : p.support.Nodup := hp.support_nodup
  have ht : t ∈ p.support := p.end_mem_support
  rw [← hc] at hnd hsub ht ⊢
  rw [List.nodup_cons] at hnd
  obtain ⟨hsn, hnd'⟩ := hnd
  have htl : t ∈ p.support.tail := by
    rcases List.mem_cons.mp ht with h | h
    · exact absurd h.symm hst
    · exact h
  have hall : ∀ x ∈ p.support.tail, x = t := by
    intro x hx
    rcases hsub x (List.mem_cons_of_mem _ hx) with h | h
    · exact absurd (h ▸ hx) hsn
    · exact h
  generalize p.support.tail = tl at *
  rcases tl with _ | ⟨a, _ | ⟨b, r⟩⟩
  · simp at htl
  · simp [hall a (by simp)]
  · have h1 := hall a (by simp)
    have h2 := hall b (by simp)
    rw [List.nodup_cons] at hnd'
    exact absurd (by simp [h1, h2]) hnd'.1

/-- A chain `s :: (m ++ [t])` is the support of a walk from `s` to `t`. -/
theorem exists_walk_full (H : SimpleGraph V) (s t : V) (m : List V)
    (hc : (s :: (m ++ [t])).IsChain H.Adj) : ∃ w : H.Walk s t, w.support = s :: (m ++ [t]) := by
  have hlast : (s :: (m ++ [t])).getLast (List.cons_ne_nil _ _) = t := by simp
  have hhead : (s :: (m ++ [t])).head (List.cons_ne_nil _ _) = s := rfl
  refine ⟨(SimpleGraph.Walk.ofSupport (s :: (m ++ [t])) (List.cons_ne_nil _ _) hc).copy hhead
    hlast, ?_⟩
  rw [SimpleGraph.Walk.support_copy]
  exact SimpleGraph.Walk.support_ofSupport _ _


/-- Decompose a list with given head and last. -/
theorem list_split {l : List V} {s t : V} (hh : l.head? = some s) (hl : l.getLast? = some t)
    (hst : s ≠ t) : ∃ m, l = s :: (m ++ [t]) := by
  rcases l with _ | ⟨a, l1⟩
  · simp at hh
  · have has : a = s := by simpa using hh
    subst has
    rcases List.eq_nil_or_concat l1 with h | ⟨m, b, h⟩
    · subst h
      simp at hl
      exact absurd hl hst
    · rw [List.concat_eq_append] at h
      subst h
      rw [← List.cons_append, List.getLast?_concat] at hl
      have hb : b = t := Option.some.inj hl
      subst hb
      exact ⟨m, rfl⟩

/-- The interior of an induced-free `s`–`t` path is an `A`–`B` path. -/
theorem ab_of_chain {H : SimpleGraph V} {s t : V} {m : List V} (S A B : Finset V)
    (hnd : (s :: (m ++ [t])).Nodup) (hch : (s :: (m ++ [t])).IsChain H.Adj) (hadj : ¬ H.Adj s t)
    (hS : ∀ v, v ≠ s → v ≠ t → v ∈ S) (hA : ∀ v, H.Adj s v → v ∈ A)
    (hB : ∀ v, H.Adj t v → v ∈ B) : IsABPath H S A B m := by
  rw [List.isChain_cons] at hch
  obtain ⟨hhead, hch'⟩ := hch
  rw [List.isChain_append] at hch'
  obtain ⟨hchm, _, hlastm⟩ := hch'
  rw [List.nodup_cons, List.nodup_append] at hnd
  obtain ⟨hsn, hndm, _, hdisj⟩ := hnd
  have hmne : m ≠ [] := by
    rintro rfl
    simp at hhead
    exact hadj hhead
  refine ⟨hmne, hndm, hchm, ?_, ?_, ?_⟩
  · intro v hv
    apply hS
    · rintro rfl; exact hsn (List.mem_append_left _ hv)
    · rintro rfl; exact hdisj v hv v (by simp) rfl
  · rcases m with _ | ⟨a, r⟩
    · exact absurd rfl hmne
    · refine ⟨a, rfl, hA a ?_⟩
      simpa using hhead
  · rcases List.eq_nil_or_concat m with h | ⟨m', b, h⟩
    · exact absurd h hmne
    · rw [List.concat_eq_append] at h
      subst h
      refine ⟨b, by simp, hB b ?_⟩
      have := hlastm b (by simp) t (by simp)
      exact this.symm


theorem chain_full {H : SimpleGraph V} {s t : V} {m : List V} (hm : m.IsChain H.Adj)
    (hne : m ≠ []) (hs : ∀ a, m.head? = some a → H.Adj s a)
    (ht : ∀ b, m.getLast? = some b → H.Adj b t) : (s :: (m ++ [t])).IsChain H.Adj := by
  rw [List.isChain_cons, List.isChain_append]
  refine ⟨?_, hm, List.IsChain.singleton t, ?_⟩
  · intro y hy
    rw [List.head?_append_of_ne_nil _ hne] at hy
    cases hh : m.head? with
    | none => simp [hh] at hy
    | some a =>
      rw [hh] at hy
      have : y = a := (Option.some.inj (Option.mem_def.mp hy)).symm
      subst this
      exact hs _ hh
  · intro x hx y hy
    have hyt : y = t := by simpa using hy.symm
    rw [hyt]
    exact ht x (Option.mem_def.mp hx)

theorem nodup_full {s t : V} {m : List V} (hm : m.Nodup) (hs : s ∉ m) (ht : t ∉ m) (hst : s ≠ t) :
    (s :: (m ++ [t])).Nodup := by
  rw [List.nodup_cons, List.nodup_append]
  refine ⟨?_, hm, List.nodup_singleton t, ?_⟩
  · simp [hs, hst]
  · intro a ha b hb
    simp at hb
    subst hb
    exact fun h => ht (h ▸ ha)

/-- Disjoint `s`–`t` walks from Menger's theorem, for non-adjacent `s`, `t`. -/
theorem nonadj_paths [Fintype V] [DecidableEq V] (H : SimpleGraph V) (s t : V) (hst : s ≠ t)
    (hadj : ¬ H.Adj s t) (k : ℕ)
    (hsep : ∀ X : Finset V, s ∉ X → t ∉ X → (∀ p : H.Walk s t, ∃ x ∈ X, x ∈ p.support) →
      k ≤ X.card) :
    ∃ P : Fin k → H.Walk s t, Function.Injective P ∧ (∀ i, (P i).IsPath) ∧
      (∀ i j, i ≠ j → ∀ x, x ∈ (P i).support → x ∈ (P j).support → x = s ∨ x = t) ∧
      ∀ i, 3 ≤ (P i).support.length := by
  classical
  set S : Finset V := Finset.univ \ {s, t} with hS
  set A : Finset V := Finset.univ.filter (fun v => H.Adj s v) with hA
  set B : Finset V := Finset.univ.filter (fun v => H.Adj t v) with hB
  have hSmem : ∀ v, v ≠ s → v ≠ t → v ∈ S := by intro v h1 h2; simp [hS, h1, h2]
  have hAmem : ∀ v, H.Adj s v → v ∈ A := by intro v h; simp [hA, h]
  have hBmem : ∀ v, H.Adj t v → v ∈ B := by intro v h; simp [hB, h]
  have hAS : A ⊆ S := by
    intro v hv
    simp only [hA, Finset.mem_filter, Finset.mem_univ, true_and] at hv
    exact hSmem v hv.ne.symm (fun h => hadj (h ▸ hv))
  have hBS : B ⊆ S := by
    intro v hv
    simp only [hB, Finset.mem_filter, Finset.mem_univ, true_and] at hv
    exact hSmem v (fun h => hadj (h ▸ hv).symm) hv.ne.symm
  have hmen : HasLinkage H S A B k := by
    refine menger_set H S A B hAS hBS k ?_
    intro X hXS hX
    have hsX : s ∉ X := fun h => by have := hXS h; simp [hS] at this
    have htX : t ∉ X := fun h => by have := hXS h; simp [hS] at this
    refine hsep X hsX htX ?_
    intro p
    have hq := p.bypass_isPath
    have hnd : p.bypass.support.Nodup := hq.support_nodup
    have hch := p.bypass.isChain_adj_support
    have hhead : p.bypass.support.head? = some s := by
      rw [List.head?_eq_some_head p.bypass.support_ne_nil, SimpleGraph.Walk.head_support]
    have hlast : p.bypass.support.getLast? = some t := by
      rw [List.getLast?_eq_some_getLast p.bypass.support_ne_nil,
        SimpleGraph.Walk.getLast_support]
    obtain ⟨m, hm⟩ := list_split hhead hlast hst
    have hpath : IsABPath H S A B m := by
      refine ab_of_chain S A B ?_ ?_ hadj hSmem hAmem hBmem
      · rw [← hm]; exact hnd
      · rw [← hm]; exact hch
    obtain ⟨x, hxX, hxm⟩ := hX m hpath
    refine ⟨x, hxX, ?_⟩
    have hx : x ∈ p.bypass.support := by rw [hm]; simp [hxm]
    exact p.support_bypass_subset_support hx
  obtain ⟨L, hL, hLp, hLd⟩ := hmen
  have hdisj : ∀ (i j : Fin k), i ≠ j → ∀ v ∈ L[i.1]'(by omega), v ∉ L[j.1]'(by omega) := by
    intro i j hij v hv hv'
    rcases lt_or_gt_of_ne (fun h => hij (Fin.ext h)) with h | h
    · exact (List.pairwise_iff_getElem.mp hLd i.1 j.1 (by omega) (by omega) h) v hv hv'
    · exact (List.pairwise_iff_getElem.mp hLd j.1 i.1 (by omega) (by omega) h) v hv' hv
  have hmp : ∀ i : Fin k, IsABPath H S A B (L[i.1]'(by omega)) := fun i =>
    hLp _ (List.getElem_mem _)
  have hnotst : ∀ (i : Fin k) v, v ∈ L[i.1]'(by omega) → v ≠ s ∧ v ≠ t := by
    intro i v hv
    have := (hmp i).2.2.2.1 v hv
    simp only [hS, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, not_or] at this
    exact this
  have hex : ∀ i : Fin k, ∃ w : H.Walk s t, w.support = s :: (L[i.1]'(by omega) ++ [t]) := by
    intro i
    obtain ⟨hne, hnd, hch, hsub, ⟨a, ha, haA⟩, ⟨b, hb, hbB⟩⟩ := hmp i
    apply exists_walk_full
    refine chain_full hch hne ?_ ?_
    · intro a' ha'
      rw [ha] at ha'
      have : a = a' := Option.some.inj ha'
      subst this
      simpa [hA] using haA
    · intro b' hb'
      rw [hb] at hb'
      have : b = b' := Option.some.inj hb'
      subst this
      have := (by simpa [hB] using hbB : H.Adj t b)
      exact this.symm
  choose P hP using hex
  have hnodup : ∀ i, (P i).support.Nodup := by
    intro i
    rw [hP i]
    refine nodup_full (hmp i).2.1 ?_ ?_ hst
    · intro h; exact (hnotst i s h).1 rfl
    · intro h; exact (hnotst i t h).2 rfl
  refine ⟨P, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    by_contra hne
    have hs := congrArg SimpleGraph.Walk.support hij
    rw [hP i, hP j] at hs
    have hm : L[i.1]'(by omega) = L[j.1]'(by omega) :=
      List.append_cancel_right (List.cons.inj hs).2
    obtain ⟨a, ha, _⟩ := (hmp i).2.2.2.2.1
    have hmem : a ∈ L[i.1]'(by omega) := by
      have hne' := (hmp i).1
      rcases hL' : L[i.1]'(by omega) with _ | ⟨a', r⟩
      · exact absurd hL' hne'
      · rw [hL'] at ha; simp at ha; simp [ha]
    exact hdisj i j hne a hmem (hm ▸ hmem)
  · intro i
    exact (SimpleGraph.Walk.isPath_def _).2 (hnodup i)
  · intro i j hij x hx hx'
    rw [hP i] at hx
    rw [hP j] at hx'
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hx hx'
    rcases hx with h | h | h
    · exact Or.inl h
    · rcases hx' with h' | h' | h'
      · exact Or.inl h'
      · exact absurd h' (hdisj i j hij x h)
      · exact Or.inr h'
    · exact Or.inr h
  · intro i
    rw [hP i]
    have := (hmp i).1
    have h2 : 0 < (L[i.1]'(by omega)).length := List.length_pos_iff.mpr this
    simp only [List.length_cons, List.length_append]
    omega


/-- Two vertices of `X` cannot be separated in `G - st` by fewer than `n - 1` vertices when `G`
is `n`-tuply connected: the bridge argument. -/
theorem bridge_sep [Fintype V] [DecidableEq V] (G : SimpleGraph V) (n' : ℕ) (s t : V) (hst : s ≠ t)
    (hcard : n' + 1 + 1 ≤ Fintype.card V)
    (hX : ∀ X : Finset V, X.card < n' + 1 → (G.induce ((↑X : Set V)ᶜ)).Connected)
    (X : Finset V) (hsX : s ∉ X) (htX : t ∉ X)
    (hsep : ∀ p : (G.deleteEdges {s(s, t)}).Walk s t, ∃ x ∈ X, x ∈ p.support) :
    n' ≤ X.card := by
  by_contra hlt
  push Not at hlt
  set H : SimpleGraph V := G.deleteEdges {s(s, t)} with hH
  have hHadj : ∀ u w, H.Adj u w ↔ G.Adj u w ∧ s(u, w) ≠ s(s, t) := by
    intro u w; simp [hH, SimpleGraph.deleteEdges_adj]
  set Y : Set V := (↑X : Set V)ᶜ with hY
  have hs : s ∈ Y := by simpa [hY] using hsX
  have ht : t ∈ Y := by simpa [hY] using htX
  set C : Set V := {v | ∃ hv : v ∈ Y, (H.induce Y).Reachable ⟨s, hs⟩ ⟨v, hv⟩} with hC
  have F1 : s ∈ C := ⟨hs, SimpleGraph.Reachable.refl _⟩
  have F2 : ∀ u w, u ∈ C → w ∈ Y → H.Adj u w → w ∈ C := by
    intro u w ⟨hu, hr⟩ hw hadj
    exact ⟨hw, hr.trans (SimpleGraph.Adj.reachable hadj)⟩
  have F3 : t ∉ C := by
    rintro ⟨ht', hr⟩
    obtain ⟨p, hp⟩ := walk_avoid H Y hs ht' hr
    obtain ⟨x, hxX, hxp⟩ := hsep p
    exact (by simpa [hY] using hp x hxp : x ∉ X) hxX
  have hcardY : 3 ≤ (Xᶜ : Finset V).card := by
    rw [Finset.card_compl]; omega
  have hsplit : (∃ c, c ∈ C ∧ c ≠ s) ∨ (∃ d, d ∈ Y ∧ d ∉ C ∧ d ≠ t) := by
    by_contra hno
    push Not at hno
    obtain ⟨h1, h2⟩ := hno
    have hsub : (Xᶜ : Finset V) ⊆ {s, t} := by
      intro v hv
      have hvY : v ∈ Y := by simpa [hY] using hv
      by_cases hvC : v ∈ C
      · simp [h1 v hvC]
      · simp [h2 v hvY hvC]
    have := Finset.card_le_card hsub
    rw [Finset.card_pair hst] at this
    omega
  rcases hsplit with ⟨c, hcC, hcs⟩ | ⟨d, hdY, hdC, hdt⟩
  · -- remove s as well
    have hcard1 : (insert s X).card < n' + 1 := by
      have := Finset.card_insert_le s X; omega
    have hc1 : c ∈ (↑(insert s X) : Set V)ᶜ := by
      obtain ⟨hcY, _⟩ := hcC
      simp only [Set.mem_compl_iff, Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe, not_or]
      exact ⟨hcs, by simpa [hY] using hcY⟩
    have ht1 : t ∈ (↑(insert s X) : Set V)ᶜ := by
      simp only [Set.mem_compl_iff, Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe, not_or]
      exact ⟨hst.symm, htX⟩
    obtain ⟨w⟩ := (hX _ hcard1).preconnected ⟨c, hc1⟩ ⟨t, ht1⟩
    have hclosed : ∀ (u w : ↥((↑(insert s X) : Set V)ᶜ)),
        (G.induce ((↑(insert s X) : Set V)ᶜ)).Adj u w → u.1 ∈ C → w.1 ∈ C := by
      intro u w hadj hu
      have hu' := u.2
      have hw' := w.2
      simp only [Set.mem_compl_iff, Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe,
        not_or] at hu' hw'
      refine F2 u.1 w.1 hu (by simpa [hY] using hw'.2) ((hHadj _ _).2 ⟨hadj, ?_⟩)
      intro heq
      rcases Sym2.eq_iff.mp heq with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact hu'.1 h1
      · exact F3 (h1 ▸ hu)
    have := walk_closed (fun v : ↥((↑(insert s X) : Set V)ᶜ) => v.1 ∈ C) hclosed w hcC
    exact F3 this
  · -- remove t as well
    have hcard2 : (insert t X).card < n' + 1 := by
      have := Finset.card_insert_le t X; omega
    have hd2 : d ∈ (↑(insert t X) : Set V)ᶜ := by
      simp only [Set.mem_compl_iff, Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe, not_or]
      exact ⟨hdt, by simpa [hY] using hdY⟩
    have hs2 : s ∈ (↑(insert t X) : Set V)ᶜ := by
      simp only [Set.mem_compl_iff, Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe, not_or]
      exact ⟨hst, hsX⟩
    obtain ⟨w⟩ := (hX _ hcard2).preconnected ⟨d, hd2⟩ ⟨s, hs2⟩
    have hclosed : ∀ (u w : ↥((↑(insert t X) : Set V)ᶜ)),
        (G.induce ((↑(insert t X) : Set V)ᶜ)).Adj u w → u.1 ∉ C → w.1 ∉ C := by
      intro u w hadj hu hwC
      have hu' := u.2
      have hw' := w.2
      simp only [Set.mem_compl_iff, Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe,
        not_or] at hu' hw'
      refine hu (F2 w.1 u.1 hwC (by simpa [hY] using hu'.2) ((hHadj _ _).2 ⟨hadj.symm, ?_⟩))
      intro heq
      rcases Sym2.eq_iff.mp heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact hu'.1 h2
      · exact F3 (h1 ▸ hwC)
    have := walk_closed (fun v : ↥((↑(insert t X) : Set V)ᶜ) => v.1 ∉ C) hclosed w hdC
    exact this F1


/-- n-tuple connectivity gives n internally disjoint paths (Menger/Whitney). -/
theorem forward [Fintype V] (G : SimpleGraph V) (n : ℕ) (hconn : IsNTuplyConnected G n)
    (s t : V) (hst : s ≠ t) : HasNDisjointPaths G n s t := by
  classical
  obtain ⟨hcard, hX⟩ := hconn
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨fun i => i.elim0, fun a => a.elim0, fun i => i.elim0, fun i => i.elim0⟩
  by_cases hadj : G.Adj s t
  · obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    set H : SimpleGraph V := G.deleteEdges {s(s, t)} with hH
    have hle : H ≤ G := SimpleGraph.deleteEdges_le _
    have hHadj : ¬ H.Adj s t := by simp [hH, SimpleGraph.deleteEdges_adj]
    obtain ⟨P, hinj, hpath, hdis, hlen⟩ := nonadj_paths H s t hst hHadj n' (fun X hsX htX hsep =>
      bridge_sep G n' s t hst hcard hX X hsX htX hsep)
    let e : G.Walk s t := SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil
    have he : e.support = [s, t] := by simp [e]
    have hsupp : ∀ i, ((P i).mapLe hle).support = (P i).support := fun i =>
      SimpleGraph.Walk.support_mapLe_eq_support _ _
    refine ⟨Fin.cons e (fun i => (P i).mapLe hle), ?_, ?_, ?_⟩
    · rw [Fin.cons_injective_iff]
      refine ⟨?_, ?_⟩
      · rintro ⟨i, hi⟩
        have hi' : (P i).mapLe hle = e := hi
        have h1 : ((P i).mapLe hle).support = e.support := congrArg SimpleGraph.Walk.support hi'
        rw [hsupp, he] at h1
        have h2 := congrArg List.length h1
        have h3 := hlen i
        simp only [List.length_cons, List.length_nil] at h2
        omega
      · intro i j hij
        apply hinj
        apply SimpleGraph.Walk.ext_support
        rw [← hsupp i, ← hsupp j]
        exact congrArg SimpleGraph.Walk.support hij
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [Fin.cons_zero]
        simp [e, SimpleGraph.Walk.cons_isPath_iff, hst]
      · simp only [Fin.cons_succ]
        rw [SimpleGraph.Walk.isPath_def, hsupp]
        exact (hpath j).support_nodup
    · intro i j hij x hx hx'
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
      · simp only [Fin.cons_zero, he] at hx
        simpa using hx
      · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
        · simp only [Fin.cons_zero, he] at hx'
          simpa using hx'
        · simp only [Fin.cons_succ, hsupp] at hx hx'
          exact hdis i' j' (fun h => hij (by rw [h])) x hx hx'
  · obtain ⟨P, hinj, hpath, hdis, _⟩ := nonadj_paths G s t hst hadj n (by
      intro X hsX htX hsepX
      by_contra hlt
      push Not at hlt
      have hs : s ∈ (↑X : Set V)ᶜ := by simpa using hsX
      have ht : t ∈ (↑X : Set V)ᶜ := by simpa using htX
      obtain ⟨p, hp⟩ := walk_avoid G _ hs ht ((hX X hlt).preconnected ⟨s, hs⟩ ⟨t, ht⟩)
      obtain ⟨x, hxX, hxp⟩ := hsepX p
      exact (by simpa using hp x hxp : x ∉ X) hxX)
    exact ⟨P, hinj, hpath, hdis⟩


/-- Counting: `n` internally disjoint paths between two vertices force `n + 1 ≤ |V|`. -/
theorem card_bound [Fintype V] (G : SimpleGraph V) (n : ℕ) (hcard : 2 ≤ Fintype.card V)
    (H : ∀ ps pk : V, ps ≠ pk → HasNDisjointPaths G n ps pk) : n + 1 ≤ Fintype.card V := by
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · omega
  obtain ⟨s, t, hst⟩ := Fintype.one_lt_card_iff.mp (by omega : 1 < Fintype.card V)
  obtain ⟨P, hinj, hpath, hdis⟩ := H s t hst
  set int : Fin n → Finset V := fun i => (P i).support.toFinset \ {s, t} with hint
  have hdisj : ∀ i ∈ (Finset.univ : Finset (Fin n)), ∀ j ∈ (Finset.univ : Finset (Fin n)),
      i ≠ j → Disjoint (int i) (int j) := by
    intro i _ j _ hij
    rw [Finset.disjoint_left]
    intro x hxi hxj
    simp only [hint, Finset.mem_sdiff, List.mem_toFinset, Finset.mem_insert,
      Finset.mem_singleton, not_or] at hxi hxj
    rcases hdis i j hij x hxi.1 hxj.1 with h | h
    · exact hxi.2.1 h
    · exact hxi.2.2 h
  have hone : (Finset.univ.filter (fun i : Fin n => int i = ∅)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro i hi j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
    by_contra hne
    have key : ∀ k, int k = ∅ → (P k).support = [s, t] := by
      intro k hk
      apply support_eq_pair (P k) (hpath k) hst
      intro x hx
      by_contra hx'
      push Not at hx'
      have : x ∈ int k := by simp [hint, hx, hx'.1, hx'.2]
      rw [hk] at this
      simp at this
    exact hne (hinj (SimpleGraph.Walk.ext_support ((key i hi).trans (key j hj).symm)))
  have h3 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
    (fun i : Fin n => int i = ∅)
  have h2 : (Finset.univ.filter (fun i : Fin n => ¬ int i = ∅)).card ≤
      ∑ i : Fin n, (int i).card := by
    calc (Finset.univ.filter (fun i : Fin n => ¬ int i = ∅)).card
        = ∑ _i ∈ Finset.univ.filter (fun i : Fin n => ¬ int i = ∅), 1 := by simp
      _ ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin n => ¬ int i = ∅), (int i).card := by
          apply Finset.sum_le_sum
          intro i hi
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
          exact Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hi)
      _ ≤ ∑ i : Fin n, (int i).card := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  have hdisj2 : Disjoint ({s, t} : Finset V) (Finset.univ.biUnion int) := by
    rw [Finset.disjoint_left]
    intro x hx hxb
    rw [Finset.mem_biUnion] at hxb
    obtain ⟨i, _, hi⟩ := hxb
    simp only [hint, Finset.mem_sdiff] at hi
    exact hi.2 hx
  have hU := Finset.card_le_card (Finset.subset_univ (({s, t} : Finset V) ∪ Finset.univ.biUnion int))
  rw [Finset.card_union_of_disjoint hdisj2, Finset.card_biUnion hdisj, Finset.card_pair hst,
    Finset.card_univ] at hU
  simp only [Finset.card_univ, Fintype.card_fin] at h3
  omega

/-- `n` internally disjoint paths between any two vertices give `n`-tuple connectivity. -/
theorem backward [Fintype V] (G : SimpleGraph V) (n : ℕ) (hcard : 2 ≤ Fintype.card V)
    (H : ∀ ps pk : V, ps ≠ pk → HasNDisjointPaths G n ps pk) : IsNTuplyConnected G n := by
  classical
  have hbound := card_bound G n hcard H
  refine ⟨hbound, ?_⟩
  intro X hX
  have hnon : Nonempty ↥((↑X : Set V)ᶜ) := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    have hall : X = Finset.univ := by
      rw [Finset.eq_univ_iff_forall]
      intro v
      by_contra hv
      exact hne.false ⟨v, by simpa using hv⟩
    rw [hall, Finset.card_univ] at hX
    omega
  rw [SimpleGraph.connected_iff]
  refine ⟨?_, hnon⟩
  intro u w
  by_cases huw : u = w
  · subst huw
    exact SimpleGraph.Reachable.refl _
  · have hne : u.1 ≠ w.1 := fun h => huw (Subtype.ext h)
    obtain ⟨P, hinj, hpath, hdis⟩ := H u.1 w.1 hne
    have hex : ∃ i, ∀ x ∈ (P i).support, x ∉ X := by
      by_contra hcon
      push Not at hcon
      choose f hf1 hf2 using hcon
      have hfinj : Function.Injective f := by
        intro i j hij
        by_contra hne'
        have h1 := hf1 i
        have h2 := hf1 j
        rw [← hij] at h2
        have hu : u.1 ∉ X := fun h => u.2 (Finset.mem_coe.mpr h)
        have hw : w.1 ∉ X := fun h => w.2 (Finset.mem_coe.mpr h)
        rcases hdis i j hne' _ h1 h2 with h | h
        · exact hu (h ▸ hf2 i)
        · exact hw (h ▸ hf2 i)
      have := Finset.card_le_card_of_injOn f (s := Finset.univ) (t := X)
        (fun i _ => hf2 i) (fun i _ j _ h => hfinj h)
      simp only [Finset.card_univ, Fintype.card_fin] at this
      omega
    obtain ⟨i, hi⟩ := hex
    exact ⟨(P i).induce _ (fun x hx => by simpa using hi x hx)⟩

end SPGTLib.Whitney

open Balinski61.Whitney in
theorem solution {V : Type*} [Fintype V] (G : SimpleGraph V) (n : ℕ)
    (hcard : 2 ≤ Fintype.card V) :
    IsNTuplyConnected G n ↔ ∀ ps pk : V, ps ≠ pk → HasNDisjointPaths G n ps pk :=
  ⟨fun h ps pk hne => SPGTLib.Whitney.forward G n h ps pk hne,
    fun h => SPGTLib.Whitney.backward G n hcard h⟩
