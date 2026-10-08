-- Prove2me | solution 1 for BergeMatching.Core.theorem_1_if
-- status  : ACCEPTED   (prove)
-- author  : @Tim
-- created : 2026-10-05T15:20:51.403636+00:00
-- url     : https://prove2.me/submissions/083903b0-6d34-480f-a6cf-e839d785d743

import Mathlib
import Definitions.Def_BergeMatching_Core_AlternatingChain

namespace BergeMatching.Core

open SimpleGraph

/-- Edges of `S` pairwise share no vertex. -/
private def EdgeDisj {V : Type} (S : Set (Sym2 V)) : Prop :=
  ∀ e ∈ S, ∀ f ∈ S, ∀ x, x ∈ e → x ∈ f → e = f

private lemma edgeDisj_of_isMatching {V : Type} {G : SimpleGraph V} {M : G.Subgraph}
    (hM : M.IsMatching) : EdgeDisj M.edgeSet := by
  intro e he f hf x hxe hxf
  obtain ⟨y, rfl⟩ := Sym2.mem_iff_exists.mp hxe
  obtain ⟨z, rfl⟩ := Sym2.mem_iff_exists.mp hxf
  rw [Subgraph.mem_edgeSet] at he hf
  rw [hM.eq_of_adj_left he hf]

/-- A vertex-disjoint set of non-loop edges covers exactly twice as many vertices as it has
edges. -/
private lemma ncard_verts {V : Type} [Fintype V] [DecidableEq V] (S : Set (Sym2 V))
    (hS : EdgeDisj S) (hd : ∀ e ∈ S, ¬ e.IsDiag) :
    {x | ∃ e ∈ S, x ∈ e}.ncard = 2 * S.ncard := by
  classical
  have hset : {x | ∃ e ∈ S, x ∈ e} = ↑(S.toFinset.biUnion (fun e => e.toFinset)) := by
    ext x; simp
  rw [hset, Set.ncard_coe_finset, Finset.card_biUnion, Set.ncard_eq_toFinset_card']
  · rw [Finset.sum_congr rfl (g := fun _ => 2), Finset.sum_const, smul_eq_mul, mul_comm]
    intro e he
    exact Sym2.card_toFinset_of_not_isDiag e (hd e (by simpa using he))
  · intro e he f hf hef
    show Disjoint e.toFinset f.toFinset
    rw [Finset.disjoint_left]
    intro x hxe hxf
    simp only [Sym2.mem_toFinset] at hxe hxf
    exact hef (hS e (by simpa using he) f (by simpa using hf) x hxe hxf)

/-- If `N'` has more edges than `N`, some vertex is an endpoint of an edge of `N' \ N` and is
not covered by `N` at all. -/
private lemma exists_start {V : Type} [Fintype V] [DecidableEq V] (N N' : Set (Sym2 V))
    (hN : EdgeDisj N) (hN' : EdgeDisj N') (hdN : ∀ e ∈ N, ¬ e.IsDiag)
    (hdN' : ∀ e ∈ N', ¬ e.IsDiag) (hlt : N.ncard < N'.ncard) :
    ∃ x y : V, s(x, y) ∈ N' ∧ s(x, y) ∉ N ∧ ∀ f ∈ N, x ∉ f := by
  by_contra hcon
  push Not at hcon
  have hsub : {x | ∃ e ∈ N' \ N, x ∈ e} ⊆ {x | ∃ e ∈ N \ N', x ∈ e} := by
    rintro x ⟨e, ⟨heN', heN⟩, hxe⟩
    obtain ⟨y, rfl⟩ := Sym2.mem_iff_exists.mp hxe
    obtain ⟨f, hfN, hxf⟩ := hcon x y heN' heN
    refine ⟨f, ⟨hfN, fun hfN' => ?_⟩, hxf⟩
    have := hN' f hfN' _ heN' x hxf hxe
    exact heN (this ▸ hfN)
  have h1 := ncard_verts (N' \ N) (fun e he f hf => hN' e he.1 f hf.1) (fun e he => hdN' e he.1)
  have h2 := ncard_verts (N \ N') (fun e he f hf => hN e he.1 f hf.1) (fun e he => hdN e he.1)
  have h3 := Set.ncard_le_ncard hsub
  have h4 := Set.ncard_inter_add_ncard_diff_eq_ncard N N'
  have h5 := Set.ncard_inter_add_ncard_diff_eq_ncard N' N
  rw [Set.inter_comm] at h5
  omega

/-- The endpoint of a nontrivial walk lies on one of its edges. -/
private lemma exists_edge_start {V : Type} {G : SimpleGraph V} {z w : V} (q : G.Walk z w)
    (h : z ≠ w) : ∃ e ∈ q.edges, z ∈ e := by
  cases q with
  | nil => exact absurd rfl h
  | cons hadj p => exact ⟨_, List.mem_cons_self .., Sym2.mem_mk_left _ _⟩

/-- A trail all of whose edges lie in the symmetric difference of two matchings alternates
with respect to the first one. -/
private theorem alt_of_symmDiff {V : Type} {G : SimpleGraph V} (N N' : Set (Sym2 V))
    (hN : EdgeDisj N) (hN' : EdgeDisj N') :
    ∀ {u v : V} (q : G.Walk u v), q.IsTrail → (∀ e ∈ q.edges, e ∈ symmDiff N N') →
      q.edges.IsChain (fun e e' => (e ∈ N ↔ e' ∉ N))
  | _, _, .nil, _, _ => by simp
  | _, _, .cons _ .nil, _, _ => by simp
  | u, _, .cons (v := b) h (.cons (v := c) h' r), ht, hD => by
    rw [Walk.edges_cons, Walk.edges_cons, List.isChain_cons_cons]
    have ht' := ht
    rw [Walk.isTrail_cons] at ht'
    obtain ⟨htail, hnot⟩ := ht'
    refine ⟨?_, ?_⟩
    · have hne : s(u, b) ≠ s(b, c) := fun heq => hnot (by simp [heq])
      have h1 := hD s(u, b) (by simp)
      have h2 := hD s(b, c) (by simp)
      rw [Set.mem_symmDiff] at h1 h2
      constructor
      · intro hub hbc
        exact hne (hN _ hub _ hbc b (Sym2.mem_mk_right _ _) (Sym2.mem_mk_left _ _))
      · intro hbc
        by_contra hub
        have hub' : s(u, b) ∈ N' := by tauto
        have hbc' : s(b, c) ∈ N' := by tauto
        exact hne (hN' _ hub' _ hbc' b (Sym2.mem_mk_right _ _) (Sym2.mem_mk_left _ _))
    · have := alt_of_symmDiff N N' hN hN' (Walk.cons h' r) htail
        (fun e he => hD e (by simp only [Walk.edges_cons, List.mem_cons] at he ⊢; tauto))
      simpa using this

/-- The augmenting-chain existence statement for edge sets: if `N'` is a matching with more
edges than the matching `N`, there is a trail between two distinct `N`-neutral vertices all of
whose edges lie in `N ∆ N'`. Proved by strong induction on `|N|`. -/
private theorem exists_aug {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} :
    ∀ (n : ℕ) (N N' : Set (Sym2 V)), N.ncard = n → EdgeDisj N → EdgeDisj N' →
      N ⊆ G.edgeSet → N' ⊆ G.edgeSet → N.ncard < N'.ncard →
      ∃ (x y : V) (q : G.Walk x y), x ≠ y ∧ (∀ e ∈ N, x ∉ e) ∧ (∀ e ∈ N, y ∉ e) ∧
        q.IsTrail ∧ ∀ e ∈ q.edges, e ∈ symmDiff N N' := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro N N' hn hN hN' hNG hN'G hlt
  have hdN : ∀ e ∈ N, ¬ e.IsDiag := fun e he => G.not_isDiag_of_mem_edgeSet (hNG he)
  have hdN' : ∀ e ∈ N', ¬ e.IsDiag := fun e he => G.not_isDiag_of_mem_edgeSet (hN'G he)
  obtain ⟨x, x₁, he₀N', he₀N, hx⟩ := exists_start N N' hN hN' hdN hdN' hlt
  have hadj : G.Adj x x₁ := hN'G he₀N'
  have he₀D : s(x, x₁) ∈ symmDiff N N' := Or.inr ⟨he₀N', he₀N⟩
  by_cases hx₁ : ∀ f ∈ N, x₁ ∉ f
  · -- the single edge `x x₁` is already augmenting
    refine ⟨x, x₁, Walk.cons hadj Walk.nil, hadj.ne, hx, hx₁, by simp, ?_⟩
    intro e he
    simp only [Walk.edges_cons, Walk.edges_nil, List.mem_singleton] at he
    exact he ▸ he₀D
  push Not at hx₁
  obtain ⟨f, hfN, hx₁f⟩ := hx₁
  obtain ⟨x₂, rfl⟩ := Sym2.mem_iff_exists.mp hx₁f
  have hadj₂ : G.Adj x₁ x₂ := hNG hfN
  have hfN' : s(x₁, x₂) ∉ N' := by
    intro hfN'
    have := hN' _ hfN' _ he₀N' x₁ (Sym2.mem_mk_left _ _) (Sym2.mem_mk_right _ _)
    exact he₀N (this ▸ hfN)
  have hfD : s(x₁, x₂) ∈ symmDiff N N' := Or.inl ⟨hfN, hfN'⟩
  have hne₀f : s(x, x₁) ≠ s(x₁, x₂) := fun h => he₀N (h ▸ hfN)
  -- remove `f = x₁ x₂` from `N` and `e₀ = x x₁` from `N'`
  set N₁ := N \ {s(x₁, x₂)} with hN₁def
  set N₁' := N' \ {s(x, x₁)} with hN₁'def
  have hcardN : N₁.ncard + 1 = N.ncard := Set.ncard_diff_singleton_add_one hfN
  have hcardN' : N₁'.ncard + 1 = N'.ncard := Set.ncard_diff_singleton_add_one he₀N'
  obtain ⟨z, w, q, hzw, hz, hw, hqt, hqD⟩ :=
    ih N₁.ncard (by omega) N₁ N₁' rfl (fun e he g hg => hN e he.1 g hg.1)
      (fun e he g hg => hN' e he.1 g hg.1) (fun e he => hNG he.1) (fun e he => hN'G he.1)
      (by omega)
  -- the reduced symmetric difference sits inside the old one and misses `e₀` and `f`
  have hD₁ : ∀ g ∈ symmDiff N₁ N₁', g ∈ symmDiff N N' ∧ g ≠ s(x, x₁) ∧ g ≠ s(x₁, x₂) := by
    intro g hg
    rcases hg with ⟨⟨hgN, hgf⟩, hgN₁'⟩ | ⟨⟨hgN', hge⟩, hgN₁⟩
    · have hge : g ≠ s(x, x₁) := fun h => he₀N (h ▸ hgN)
      refine ⟨Or.inl ⟨hgN, fun hgN' => hgN₁' ⟨hgN', hge⟩⟩, hge, hgf⟩
    · have hgf : g ≠ s(x₁, x₂) := fun h => hfN' (h ▸ hgN')
      refine ⟨Or.inr ⟨hgN', fun hgN => hgN₁ ⟨hgN, hgf⟩⟩, hge, hgf⟩
  have hxD₁ : ∀ g ∈ symmDiff N₁ N₁', x ∉ g := by
    intro g hg hxg
    rcases hg with ⟨⟨hgN, -⟩, -⟩ | ⟨⟨hgN', hge⟩, -⟩
    · exact hx g hgN hxg
    · exact hge (hN' g hgN' _ he₀N' x hxg (Sym2.mem_mk_left _ _))
  have hx₁D₁ : ∀ g ∈ symmDiff N₁ N₁', x₁ ∉ g := by
    intro g hg hxg
    rcases hg with ⟨⟨hgN, hgf⟩, -⟩ | ⟨⟨hgN', hge⟩, -⟩
    · exact hgf (hN g hgN _ hfN x₁ hxg (Sym2.mem_mk_left _ _))
    · exact hge (hN' g hgN' _ he₀N' x₁ hxg (Sym2.mem_mk_right _ _))
  -- an `N₁`-neutral endpoint of `q` other than `x₂` is `N`-neutral
  have hneut : ∀ y, y ≠ x₁ → y ≠ x₂ → (∀ e ∈ N₁, y ∉ e) → ∀ e ∈ N, y ∉ e := by
    intro y hy1 hy2 hy e he hye
    by_cases hef : e = s(x₁, x₂)
    · subst hef
      rcases Sym2.mem_iff.mp hye with h | h
      · exact hy1 h
      · exact hy2 h
    · exact hy e ⟨he, hef⟩ hye
  -- endpoints of `q` lie on edges of `q`, hence avoid `x` and `x₁`
  have hend : ∀ {a b : V} (r : G.Walk a b), a ≠ b →
      (∀ e ∈ r.edges, e ∈ symmDiff N₁ N₁') → a ≠ x ∧ a ≠ x₁ := by
    intro a b r hab hr
    obtain ⟨g, hg, hag⟩ := exists_edge_start r hab
    exact ⟨fun h => hxD₁ g (hr g hg) (h ▸ hag), fun h => hx₁D₁ g (hr g hg) (h ▸ hag)⟩
  -- if `q` starts at `x₂`, prepend `x x₁ x₂`
  have key : ∀ (w : V) (q : G.Walk x₂ w), x₂ ≠ w → q.IsTrail →
      (∀ e ∈ q.edges, e ∈ symmDiff N₁ N₁') → (∀ e ∈ N₁, w ∉ e) →
      ∃ (x y : V) (q : G.Walk x y), x ≠ y ∧ (∀ e ∈ N, x ∉ e) ∧ (∀ e ∈ N, y ∉ e) ∧
        q.IsTrail ∧ ∀ e ∈ q.edges, e ∈ symmDiff N N' := by
    intro w q hx₂w hqt hqD hw
    have hrevD : ∀ e ∈ q.reverse.edges, e ∈ symmDiff N₁ N₁' := by
      intro e he; rw [Walk.edges_reverse, List.mem_reverse] at he; exact hqD e he
    obtain ⟨hwx, hwx₁⟩ := hend q.reverse (Ne.symm hx₂w) hrevD
    refine ⟨x, w, Walk.cons hadj (Walk.cons hadj₂ q), Ne.symm hwx, hx,
      hneut w hwx₁ (Ne.symm hx₂w) hw, ?_, ?_⟩
    · rw [Walk.isTrail_cons, Walk.isTrail_cons]
      refine ⟨⟨hqt, fun h => (hD₁ _ (hqD _ h)).2.2 rfl⟩, ?_⟩
      simp only [Walk.edges_cons, List.mem_cons, not_or]
      exact ⟨hne₀f, fun h => (hD₁ _ (hqD _ h)).2.1 rfl⟩
    · intro e he
      simp only [Walk.edges_cons, List.mem_cons] at he
      rcases he with rfl | rfl | he
      · exact he₀D
      · exact hfD
      · exact (hD₁ e (hqD e he)).1
  by_cases hz₂ : z = x₂
  · subst hz₂
    exact key w q hzw hqt hqD hw
  by_cases hw₂ : w = x₂
  · subst hw₂
    refine key z q.reverse (Ne.symm hzw) (hqt.reverse) ?_ hz
    intro e he; rw [Walk.edges_reverse, List.mem_reverse] at he; exact hqD e he
  -- otherwise `q` itself works
  obtain ⟨-, hzx₁⟩ := hend q hzw hqD
  have hrevD : ∀ e ∈ q.reverse.edges, e ∈ symmDiff N₁ N₁' := by
    intro e he; rw [Walk.edges_reverse, List.mem_reverse] at he; exact hqD e he
  obtain ⟨-, hwx₁⟩ := hend q.reverse (Ne.symm hzw) hrevD
  exact ⟨z, w, q, hzw, hneut z hzx₁ hz₂ hz, hneut w hwx₁ hw₂ hw, hqt,
    fun e he => (hD₁ e (hqD e he)).1⟩

end BergeMatching.Core

open BergeMatching.Core

theorem solution {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (M : G.Subgraph) (hM : M.IsMatching) (hnot : ¬ IsMaximumMatching M) :
    ∃ (a a' : V) (p : G.Walk a a'),
      a ≠ a' ∧ IsNeutral M a ∧ IsNeutral M a' ∧ IsAlternatingChain M p := by
  have : ∃ M' : G.Subgraph, M'.IsMatching ∧ M.edgeSet.ncard < M'.edgeSet.ncard := by
    by_contra h
    push Not at h
    exact hnot ⟨hM, h⟩
  obtain ⟨M', hM', hlt⟩ := this
  have hN := edgeDisj_of_isMatching hM
  have hN' := edgeDisj_of_isMatching hM'
  obtain ⟨x, y, q, hxy, hx, hy, hqt, hqD⟩ :=
    exists_aug _ M.edgeSet M'.edgeSet rfl hN hN' M.edgeSet_subset M'.edgeSet_subset hlt
  exact ⟨x, y, q, hxy, hx, hy, hqt, alt_of_symmDiff _ _ hN hN' q hqt hqD⟩
