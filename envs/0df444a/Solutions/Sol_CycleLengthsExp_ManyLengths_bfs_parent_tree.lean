-- Prove2me | solution 1 for CycleLengthsExp.ManyLengths.bfs_parent_tree
-- status  : ACCEPTED   (prove)
-- author  : @junyihjy
-- created : 2026-10-19T04:40:37.800546+00:00
-- url     : https://prove2.me/submissions/6df52897-2c91-471e-b3ed-d8e59c22dad8

import Mathlib
import Definitions.Def_CycleLengthsExp_ManyLengths_Setting

set_option autoImplicit false

open SimpleGraph

theorem solution {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (S : Set V) (v₀ : V) (hv₀ : v₀ ∈ S)
    (hreach : ∀ v ∈ S, G.Reachable v₀ v)
    (hparent : ∀ v ∈ S, v ≠ v₀ →
      ∃ u ∈ S, G.Adj u v ∧ G.dist v₀ u + 1 = G.dist v₀ v) :
    ∃ T : G.Subgraph, T.verts = S ∧ T.spanningCoe.IsAcyclic ∧
      (∀ v ∈ S, T.spanningCoe.Reachable v₀ v) ∧
      (∀ v ∈ S, T.spanningCoe.dist v₀ v = G.dist v₀ v) := by
  classical
  -- Parent function from the hypothesis, pinned at the root.
  -- First totalize the choice so `choose` yields a plain `V → V`.
  have hex : ∀ v : V, ∃ u : V,
      (v ∈ S ∧ v ≠ v₀ → u ∈ S ∧ G.Adj u v ∧ G.dist v₀ u + 1 = G.dist v₀ v) ∧
        (v = v₀ → u = v₀) := by
    intro v
    by_cases hv : v ∈ S ∧ v ≠ v₀
    · obtain ⟨u, huS, hAdj, hdist⟩ := hparent v hv.1 hv.2
      exact ⟨u, fun _ => ⟨huS, hAdj, hdist⟩, fun hEq => absurd hEq hv.2⟩
    · exact ⟨v₀, fun h => absurd h hv, fun _ => rfl⟩
  choose par' hpar' using hex
  have hpar'0 : par' v₀ = v₀ := (hpar' v₀).2 rfl
  have hpar'' : ∀ v ∈ S, v ≠ v₀ →
      par' v ∈ S ∧ G.Adj (par' v) v ∧ G.dist v₀ (par' v) + 1 = G.dist v₀ v :=
    fun v hv hne => (hpar' v).1 ⟨hv, hne⟩
  -- T: the parent-edge subgraph on S.
  set T : G.Subgraph :=
    { verts := S
      Adj := fun u v => u ∈ S ∧ v ∈ S ∧ u ≠ v ∧ (par' u = v ∨ par' v = u)
      adj_sub := by
        intro u v h
        obtain ⟨huS, hvS, huv, hpar⟩ := h
        rcases hpar with h1 | h1
        · have hu0 : u ≠ v₀ := by
            rintro rfl
            rw [hpar'0] at h1
            exact huv h1
          obtain ⟨_, hAdj, _⟩ := hpar'' u huS hu0
          rw [h1] at hAdj
          exact hAdj.symm
        · have hv0 : v ≠ v₀ := by
            rintro rfl
            rw [hpar'0] at h1
            exact huv h1.symm
          obtain ⟨_, hAdj, _⟩ := hpar'' v hvS hv0
          rw [h1] at hAdj
          exact hAdj
      edge_vert := by
        intro u v h
        exact h.1
      symm := ⟨fun {u v} h =>
        ⟨h.2.1, h.1, h.2.2.1.symm, h.2.2.2.symm⟩⟩ } with hTdef
  have hTverts : T.verts = S := by rw [hTdef]
  have hTadj_iff : ∀ {u v : V}, T.Adj u v ↔
      (u ∈ S ∧ v ∈ S ∧ u ≠ v ∧ (par' u = v ∨ par' v = u)) := by
    intro u v
    rw [hTdef]
  -- Parent chain: a T-walk from v to v₀ of length dist_G(v₀, v).
  have hchain : ∀ k : ℕ, ∀ v ∈ S, G.dist v₀ v = k →
      ∃ p : T.spanningCoe.Walk v v₀, p.length = k := by
    intro k
    induction k with
    | zero =>
      intro v hv hd
      have hv0 : v = v₀ := by
        have h0 := hd
        rw [SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable] at h0
        rcases h0 with hEq | hnr
        · exact hEq.symm
        · exact absurd (hreach v hv) hnr
      subst hv0
      exact ⟨Walk.nil, rfl⟩
    | succ k ih =>
      intro v hv hd
      have hne : v ≠ v₀ := by
        rintro rfl
        simp at hd
      obtain ⟨hparS, _hparAdj, hparDist⟩ := hpar'' v hv hne
      have hdk : G.dist v₀ (par' v) = k := by omega
      obtain ⟨p, hp⟩ := ih (par' v) hparS hdk
      have hne2 : v ≠ par' v := by
        rintro hEq
        rw [← hEq] at hparDist
        omega
      have hT : T.Adj v (par' v) :=
        hTadj_iff.mpr ⟨hv, hparS, hne2, Or.inl rfl⟩
      have hT' : T.spanningCoe.Adj v (par' v) := by
        rw [Subgraph.spanningCoe_adj]
        exact hT
      exact ⟨Walk.cons hT' p, by simp [Walk.length_cons, hp]⟩
  have hreachT : ∀ v ∈ S, T.spanningCoe.Reachable v₀ v := by
    intro v hv
    obtain ⟨p, _hp⟩ := hchain (G.dist v₀ v) v hv rfl
    exact ⟨p.reverse⟩
  -- Every T-walk maps to a G-walk of the same length.
  have hmap : ∀ {a b : V} (p : T.spanningCoe.Walk a b),
      ∃ q : G.Walk a b, q.length = p.length := by
    intro a b p
    induction p with
    | nil => exact ⟨Walk.nil, rfl⟩
    | cons h p ih =>
      obtain ⟨q, hq⟩ := ih
      exact ⟨Walk.cons (T.adj_sub h) q, by simp [Walk.length_cons, hq]⟩
  have hdist_le : ∀ v ∈ S, T.spanningCoe.dist v₀ v ≤ G.dist v₀ v := by
    intro v hv
    obtain ⟨p, hp⟩ := hchain (G.dist v₀ v) v hv rfl
    have hle := SimpleGraph.dist_le (G := T.spanningCoe) p.reverse
    rwa [Walk.length_reverse, hp] at hle
  have hdist_ge : ∀ v ∈ S, G.dist v₀ v ≤ T.spanningCoe.dist v₀ v := by
    intro v hv
    obtain ⟨p, hp⟩ := (hreachT v hv).exists_walk_length_eq_dist
    obtain ⟨q, hq⟩ := hmap p
    have hle := SimpleGraph.dist_le (G := G) q
    rwa [hq, hp] at hle
  -- Acyclicity: a cycle's max-distance vertex would need two distinct
  -- neighbours, but only its parent can be a neighbour at ≤ its distance.
  have hacyc : T.spanningCoe.IsAcyclic := by
    intro v c hc
    obtain ⟨x0, hx0⟩ := c.support_nonempty
    have hne : c.support.toFinset.Nonempty := ⟨x0, List.mem_toFinset.mpr hx0⟩
    obtain ⟨x, hxfin, hxmax⟩ :=
      Finset.exists_max_image c.support.toFinset (fun w => G.dist v₀ w) hne
    have hx : x ∈ c.support := List.mem_toFinset.mp hxfin
    have hcard : (c.toSubgraph.neighborSet x).ncard = 2 :=
      hc.ncard_neighborSet_toSubgraph_eq_two hx
    have hsub : c.toSubgraph.neighborSet x ⊆ {par' x} := by
      intro w hw
      rw [Subgraph.mem_neighborSet] at hw
      have hmem : s(x, w) ∈ c.edges := Walk.adj_toSubgraph_iff_mem_edges.mp hw
      have hTadj : T.spanningCoe.Adj x w := c.adj_of_mem_edges hmem
      obtain ⟨_hxS, hwS, hxw, hpar⟩ := hTadj_iff.mp hTadj
      rcases hpar with h1 | h1
      · exact Set.mem_singleton_iff.mpr h1.symm
      · exfalso
        have hw0 : w ≠ v₀ := by
          rintro rfl
          rw [hpar'0] at h1
          exact hxw h1.symm
        obtain ⟨_, _, hdist⟩ := hpar'' w hwS hw0
        rw [h1] at hdist
        have hwsup : w ∈ c.support := Walk.mem_support_of_adj_toSubgraph hw.symm
        have hmax : G.dist v₀ w ≤ G.dist v₀ x :=
          hxmax w (List.mem_toFinset.mpr hwsup)
        omega
    have hle : (c.toSubgraph.neighborSet x).ncard ≤ 1 := by
      calc (c.toSubgraph.neighborSet x).ncard
          ≤ ({par' x} : Set V).ncard :=
            Set.ncard_le_ncard hsub (Set.finite_singleton _)
        _ = 1 := Set.ncard_singleton _
    omega
  exact ⟨T, hTverts, hacyc, hreachT,
    fun v hv => le_antisymm (hdist_le v hv) (hdist_ge v hv)⟩

theorem bfs_parent_tree {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (S : Set V) (v₀ : V) (hv₀ : v₀ ∈ S)
    (hreach : ∀ v ∈ S, G.Reachable v₀ v)
    (hparent : ∀ v ∈ S, v ≠ v₀ →
      ∃ u ∈ S, G.Adj u v ∧ G.dist v₀ u + 1 = G.dist v₀ v) :
    ∃ T : G.Subgraph, T.verts = S ∧ T.spanningCoe.IsAcyclic ∧
      (∀ v ∈ S, T.spanningCoe.Reachable v₀ v) ∧
      (∀ v ∈ S, T.spanningCoe.dist v₀ v = G.dist v₀ v) :=
  solution G S v₀ hv₀ hreach hparent
