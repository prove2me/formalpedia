-- Prove2me | solution 1 for CycleLengthsExp.ManyLengths.ext_parent_tree
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T23:45:31.761953+00:00
-- url     : https://prove2.me/submissions/73e68a60-2a8d-4be5-bce1-63c1b8e44291

import Mathlib
import Definitions.Def_CycleLengthsExp_ManyLengths_Setting

open CycleLengthsExp CycleLengthsExp.ManyLengths
/-- Extension parent tree (Friedman–Krivelevich, p. 14: "Extend T by adding
up to k-1 new levels using the BFS algorithm while avoiding adding vertices
of P").

Given a tree `T` on `S` (rooted at `v₀`, acyclic, reaching every vertex of
`S`) and a superset `W ⊇ S` with a height function `h` (0 on `S`, positive
off `S`) and the parent property (every `w ∈ W ∖ S` has a neighbour in `W`
with `h` one less), there is a subgraph `T₁` on exactly the vertices `W`
extending `T`, acyclic, reaching every vertex of `W` from `v₀`, with the
EXACT level formula `dist_{T₁}(v₀, w) = dist_T(v₀, r w) + h w` for a root
function `r : V → V` (the parent-chain endpoint in `S`, identity on `S`),
and every `w ∈ W ∖ S` has its root `r w` adjacent to some vertex outside
`S` (the `h = 1` vertex on `w`'s parent chain — this is what feeds the
frontier hypothesis in the assembly).

Proof sketch: choose a parent function `p` by choice from `hparent` (for
`w ∈ W ∖ S` pick `u` with `h u + 1 = h w`; `p` is only used on `W ∖ S`).
Let `T₁.verts = W` and `T₁.Adj` be `T.Adj` plus the symmetrized parent
edges. Acyclicity: max-`h` argument on closed `T₁`-paths — a vertex of
maximal `h` on a nontrivial closed path has two distinct `T₁`-neighbours,
both of `h` one less, but it has only one parent edge and `T`-edges
require `h = 0` (the all-`h = 0` case reduces to `T`-acyclicity).
Dist formula: upper bound via the `T`-path to `r w` plus the parent chain;
lower bound via the root-projection argument (every `T₁`-edge either
preserves `r` or is a `T`-edge; parent edges change `h` by exactly ±1,
so any `T₁`-path from `v₀` to `w` has length at least
`dist_T (v₀, r w) + h w`). Frontier-neighbour: the `h = 1` vertex on `w`'s
parent chain is outside `S` and adjacent to `r w`. -/
theorem h42_acyc {V : Type*} [DecidableEq V] {H H' : SimpleGraph V} (hH' : H'.IsAcyclic)
    (h : V → ℕ) (p : V → V)
    (hadj : ∀ a b, H.Adj a b → H'.Adj a b ∨ (p a = b ∧ 0 < h a ∧ h b + 1 = h a) ∨
      (p b = a ∧ 0 < h b ∧ h a + 1 = h b))
    (h0 : ∀ a b, H'.Adj a b → h a = 0) : H.IsAcyclic := by
  intro x c hc
  by_cases hpos : ∃ y ∈ c.support, 0 < h y
  · obtain ⟨y, hy, hymax⟩ := c.support.toFinset.exists_max_image h ⟨x, by simp⟩
    rw [List.mem_toFinset] at hy
    have hmax : ∀ z ∈ c.support, h z ≤ h y := fun z hz => hymax z (List.mem_toFinset.mpr hz)
    have hypos : 0 < h y := by
      obtain ⟨z, hz, hz'⟩ := hpos; exact lt_of_lt_of_le hz' (hmax z hz)
    have hc' : (c.rotate y hy).IsCycle := hc.rotate hy
    have hnn : ¬ (c.rotate y hy).Nil := hc'.not_nil
    have key : ∀ z, H.Adj y z → z ∈ (c.rotate y hy).support → z = p y := by
      intro z hyz hz
      rw [SimpleGraph.Walk.mem_support_rotate_iff] at hz
      rcases hadj y z hyz with h1 | ⟨h1, _, _⟩ | ⟨h1, _, h3⟩
      · have := h0 y z h1; omega
      · exact h1.symm
      · have := hmax z hz; omega
    have e1 := key _ (SimpleGraph.Walk.adj_snd hnn) (SimpleGraph.Walk.getVert_mem_support _ _)
    have e2 := key _ (SimpleGraph.Walk.adj_penultimate hnn).symm
      (SimpleGraph.Walk.getVert_mem_support _ _)
    exact hc'.snd_ne_penultimate (e1.trans e2.symm)
  · push Not at hpos
    have hE : ∀ e ∈ c.edges, e ∈ H'.edgeSet := by
      intro e he
      induction e using Sym2.ind with
      | h a b =>
        have ha := hpos a (c.fst_mem_support_of_mem_edges he)
        have hb := hpos b (c.snd_mem_support_of_mem_edges he)
        have hab : H.Adj a b := c.adj_of_mem_edges he
        rcases hadj a b hab with h1 | ⟨_, h2, _⟩ | ⟨_, h2, _⟩
        · exact h1
        · omega
        · omega
    exact hH' (c.transfer H' hE) (hc.transfer hE)

theorem solution {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (S : Set V) (T : G.Subgraph) (v₀ : V)
    (hTverts : T.verts = S) (hv₀ : v₀ ∈ S)
    (hTacyc : T.spanningCoe.IsAcyclic)
    (hTreach : ∀ v ∈ S, T.spanningCoe.Reachable v₀ v)
    (W : Set V) (hSW : S ⊆ W)
    (h : V → ℕ) (hhS : ∀ w ∈ S, h w = 0) (hhW : ∀ w ∈ W, w ∉ S → 0 < h w)
    (hparent : ∀ w ∈ W, w ∉ S → ∃ u ∈ W, G.Adj u w ∧ h u + 1 = h w) :
    ∃ (T₁ : G.Subgraph) (r : V → V),
      T₁.verts = W ∧
      (∀ a b, T.spanningCoe.Adj a b → T₁.spanningCoe.Adj a b) ∧
      T₁.spanningCoe.IsAcyclic ∧
      (∀ w ∈ W, T₁.spanningCoe.Reachable v₀ w) ∧
      (∀ w ∈ W, r w ∈ S) ∧
      (∀ w ∈ S, r w = w) ∧
      (∀ w ∈ W, T₁.spanningCoe.dist v₀ w = T.spanningCoe.dist v₀ (r w) + h w) ∧
      (∀ w ∈ W, w ∉ S → ∃ z, z ∉ S ∧ G.Adj (r w) z) := by
  classical
  have hpex : ∀ w, ∃ u, w ∈ W → w ∉ S → u ∈ W ∧ G.Adj u w ∧ h u + 1 = h w := by
    intro w
    by_cases hw : w ∈ W ∧ w ∉ S
    · obtain ⟨u, hu, hadj, hh⟩ := hparent w hw.1 hw.2
      exact ⟨u, fun _ _ => ⟨hu, hadj, hh⟩⟩
    · exact ⟨w, fun a b => absurd ⟨a, b⟩ hw⟩
  choose p hp using hpex
  have hWS : ∀ x ∈ W, h x = 0 → x ∈ S := by
    intro x hx h0; by_contra hxS; have := hhW x hx hxS; omega
  have hit : ∀ k x, x ∈ W → k ≤ h x → p^[k] x ∈ W ∧ h (p^[k] x) + k = h x := by
    intro k
    induction k with
    | zero => intro x hx _; exact ⟨hx, by simp⟩
    | succ k ih =>
      intro x hx hk
      obtain ⟨h1, h2⟩ := ih x hx (by omega)
      have hyS : p^[k] x ∉ S := by intro hS; have := hhS _ hS; omega
      obtain ⟨h3, _, h5⟩ := hp _ h1 hyS
      rw [Function.iterate_succ_apply']
      exact ⟨h3, by omega⟩
  let r : V → V := fun x => p^[h x] x
  have hrS : ∀ w ∈ W, r w ∈ S := by
    intro w hw
    obtain ⟨h1, h2⟩ := hit (h w) w hw le_rfl
    have h0 : h (p^[h w] w) = 0 := by omega
    exact hWS _ h1 h0
  have hrid : ∀ w ∈ S, r w = w := by
    intro w hw; show p^[h w] w = w; rw [hhS w hw]; rfl
  have hrp : ∀ x ∈ W, x ∉ S → r (p x) = r x := by
    intro x hx hxS
    have hh := (hp x hx hxS).2.2
    show p^[h (p x)] (p x) = p^[h x] x
    rw [← hh, Function.iterate_succ_apply]
  let T₁ : G.Subgraph :=
    { verts := W
      Adj := fun a b => T.Adj a b ∨ (a ∈ W ∧ a ∉ S ∧ p a = b) ∨ (b ∈ W ∧ b ∉ S ∧ p b = a)
      adj_sub := by
        rintro a b (h1 | ⟨ha, haS, rfl⟩ | ⟨hb, hbS, rfl⟩)
        · exact T.adj_sub h1
        · exact (hp a ha haS).2.1.symm
        · exact (hp b hb hbS).2.1
      edge_vert := by
        rintro a b (h1 | ⟨ha, _, _⟩ | ⟨hb, hbS, rfl⟩)
        · exact hSW (hTverts ▸ T.edge_vert h1)
        · exact ha
        · exact (hp b hb hbS).1
      symm := ⟨fun a b hab => by
        rcases hab with h1 | h2 | h3
        · exact Or.inl (T.adj_symm h1)
        · exact Or.inr (Or.inr h2)
        · exact Or.inr (Or.inl h3)⟩ }
  have hT1adj : ∀ a b, T₁.spanningCoe.Adj a b ↔
      (T.Adj a b ∨ (a ∈ W ∧ a ∉ S ∧ p a = b) ∨ (b ∈ W ∧ b ∉ S ∧ p b = a)) := fun a b => Iff.rfl
  have hTS : ∀ a b, T.Adj a b → a ∈ S := fun a b hab => hTverts ▸ T.edge_vert hab
  have hle : T.spanningCoe ≤ T₁.spanningCoe := fun a b hab => Or.inl hab
  -- upper bound walks
  have hup : ∀ k, ∀ x ∈ W, h x = k →
      ∃ q : T₁.spanningCoe.Walk v₀ x, q.length = T.spanningCoe.dist v₀ (r x) + h x := by
    intro k
    induction k with
    | zero =>
      intro x hx hx0
      have hxS := hWS x hx hx0
      obtain ⟨q, hq⟩ := (hTreach x hxS).exists_walk_length_eq_dist
      refine ⟨q.mapLe hle, ?_⟩
      rw [SimpleGraph.Walk.length_mapLe, hq, hrid x hxS, hx0]; rfl
    | succ k ih =>
      intro x hx hxk
      have hxS : x ∉ S := by intro hS; have := hhS x hS; omega
      obtain ⟨h1, _, h3⟩ := hp x hx hxS
      obtain ⟨q, hq⟩ := ih (p x) h1 (by omega)
      have hadj : T₁.spanningCoe.Adj (p x) x := Or.inr (Or.inr ⟨hx, hxS, rfl⟩)
      refine ⟨q.concat hadj, ?_⟩
      rw [SimpleGraph.Walk.length_concat, hq, hrp x hx hxS]; omega
  -- lower bound
  have hlow : ∀ a b (q : T₁.spanningCoe.Walk a b), a ∈ W →
      T.spanningCoe.dist v₀ (r a) + h a ≤ T.spanningCoe.dist v₀ (r b) + h b + q.length := by
    intro a b q
    induction q with
    | nil => intro _; simp
    | @cons a a' b hadj q ih =>
      intro ha
      have ha' : a' ∈ W := T₁.edge_vert hadj.symm
      have := ih ha'
      rw [SimpleGraph.Walk.length_cons]
      rcases hadj with h1 | ⟨_, haS, rfl⟩ | ⟨_, haS', rfl⟩
      · have haS := hTS a a' h1
        have haS' := hTS a' a (T.adj_symm h1)
        rw [hrid a haS, hrid a' haS', hhS a haS, hhS a' haS'] at *
        have hr : T.spanningCoe.Reachable a' a := (SimpleGraph.Adj.reachable (G := T.spanningCoe) (T.adj_symm h1))
        have h2 := hr.dist_triangle_right v₀
        have h3 : T.spanningCoe.dist a' a = 1 :=
          SimpleGraph.dist_eq_one_iff_adj.mpr (show T.spanningCoe.Adj a' a from T.adj_symm h1)
        omega
      · have := (hp a ha haS).2.2
        rw [← hrp a ha haS]; omega
      · have := (hp a' ha' haS').2.2
        rw [hrp a' ha' haS'] at *; omega
  have hreach : ∀ w ∈ W, T₁.spanningCoe.Reachable v₀ w := by
    intro w hw; obtain ⟨q, _⟩ := hup (h w) w hw rfl; exact ⟨q⟩
  have hfront : ∀ k, ∀ w ∈ W, w ∉ S → h w = k + 1 → ∃ z, z ∉ S ∧ G.Adj (r w) z := by
    intro k
    induction k with
    | zero =>
      intro w hw hwS hk
      obtain ⟨h1, h2, h3⟩ := hp w hw hwS
      have hpS := hWS _ h1 (by omega)
      refine ⟨w, hwS, ?_⟩
      rw [← hrp w hw hwS, hrid _ hpS]; exact h2
    | succ k ih =>
      intro w hw hwS hk
      obtain ⟨h1, _, h3⟩ := hp w hw hwS
      have hpS : p w ∉ S := by intro hS; have := hhS _ hS; omega
      rw [← hrp w hw hwS]; exact ih (p w) h1 hpS (by omega)
  refine ⟨T₁, r, rfl, fun a b hab => Or.inl hab, ?_, hreach, hrS, hrid, ?_, ?_⟩
  · refine h42_acyc hTacyc h p ?_ ?_
    · intro a b hab
      rcases hab with h1 | ⟨ha, haS, rfl⟩ | ⟨hb, hbS, rfl⟩
      · exact Or.inl h1
      · exact Or.inr (Or.inl ⟨rfl, hhW a ha haS, (hp a ha haS).2.2⟩)
      · exact Or.inr (Or.inr ⟨rfl, hhW b hb hbS, (hp b hb hbS).2.2⟩)
    · intro a b hab; exact hhS a (hTS a b hab)
  · intro w hw
    obtain ⟨q, hq⟩ := hup (h w) w hw rfl
    obtain ⟨q', hq'⟩ := (hreach w hw).exists_walk_length_eq_dist
    have h1 := hlow w v₀ q'.reverse hw
    rw [hrid v₀ hv₀, hhS v₀ hv₀, SimpleGraph.Walk.length_reverse, hq'] at h1
    simp only [SimpleGraph.dist_self] at h1
    have h2 := SimpleGraph.dist_le q
    omega
  · intro w hw hwS
    have := hhW w hw hwS
    exact hfront (h w - 1) w hw hwS (by omega)


