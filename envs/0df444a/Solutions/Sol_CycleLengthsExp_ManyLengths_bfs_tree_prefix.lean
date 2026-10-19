-- Prove2me | solution 1 for CycleLengthsExp.ManyLengths.bfs_tree_prefix
-- status  : ACCEPTED   (prove)
-- author  : @junyihjy
-- created : 2026-10-19T08:42:18.508298+00:00
-- url     : https://prove2.me/submissions/4807798c-e30e-471b-876d-b5bcf9e28403

import Mathlib
import Definitions.Def_CycleLengthsExp_ManyLengths_Setting

set_option autoImplicit false

open SimpleGraph CycleLengthsExp CycleLengthsExp.ManyLengths

theorem bfs_parent_tree_proved {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
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

theorem h42_pred {V : Type*} {G : SimpleGraph V} {v₀ v : V} (hr : G.Reachable v₀ v) (hne : v ≠ v₀) :
    ∃ u, G.Adj u v ∧ G.dist v₀ u + 1 = G.dist v₀ v := by
  obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_dist
  have hpr : p.reverse.length = G.dist v₀ v := by rw [SimpleGraph.Walk.length_reverse, hp]
  generalize p.reverse = q at hpr
  cases q with
  | nil => exact absurd rfl hne
  | @cons _ u _ h q =>
    refine ⟨u, h.symm, ?_⟩
    have h1 : G.dist u v₀ ≤ q.length := SimpleGraph.dist_le q
    rw [SimpleGraph.Walk.length_cons] at hpr
    have h2 : G.dist v₀ v ≤ G.dist v₀ u + G.dist u v := h.symm.reachable.dist_triangle_right v₀
    have h3 : G.dist u v = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr h.symm
    rw [SimpleGraph.dist_comm] at h1
    omega

theorem bfs_prefix_set_proved (n : ℕ) (G : SimpleGraph (Fin n)) (v₀ : Fin n) (N : ℕ)
    (hconn : ∀ v, G.Reachable v₀ v) (hN1 : 1 ≤ N) (hNn : N ≤ n) :
    ∃ (S : Set (Fin n)) (r : ℕ),
      S.ncard = N ∧ v₀ ∈ S ∧
      (∀ v, G.dist v₀ v ≤ r - 1 → v ∈ S) ∧
      (∀ v ∈ S, G.dist v₀ v ≤ r) ∧
      (∃ v ∈ S, G.dist v₀ v = r) ∧
      (∀ v ∈ S, v ≠ v₀ →
        ∃ u ∈ S, G.Adj u v ∧ G.dist v₀ u + 1 = G.dist v₀ v) := by
  classical
  let B : ℕ → Finset (Fin n) := fun k => Finset.univ.filter (fun v => G.dist v₀ v ≤ k)
  have hex : ∃ k, N ≤ (B k).card := by
    refine ⟨Finset.univ.sup (fun v => G.dist v₀ v), ?_⟩
    have : B (Finset.univ.sup (fun v => G.dist v₀ v)) = Finset.univ := by
      ext v; simp only [B, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      exact Finset.le_sup (f := fun v => G.dist v₀ v) (Finset.mem_univ v)
    rw [this, Finset.card_univ, Fintype.card_fin]; exact hNn
  let r := Nat.find hex
  have hr : N ≤ (B r).card := Nat.find_spec hex
  let A : Finset (Fin n) := Finset.univ.filter (fun v => G.dist v₀ v < r)
  let Sp : Finset (Fin n) := Finset.univ.filter (fun v => G.dist v₀ v = r)
  have hA : A.card < N := by
    by_cases h0 : r = 0
    · have : A = ∅ := by
        ext v; simp only [A, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]; omega
      rw [this, Finset.card_empty]; omega
    · have hm := Nat.find_min hex (show r - 1 < r by omega)
      have : A = B (r - 1) := by
        ext v; simp only [A, B, Finset.mem_filter, Finset.mem_univ, true_and]; omega
      rw [this]; omega
  have hBr : B r = A ∪ Sp := by
    ext v; simp only [A, B, Sp, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]; omega
  have hdisj : Disjoint A Sp := by
    rw [Finset.disjoint_left]; intro v h1 h2
    simp only [A, Sp, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2; omega
  have hSp : N - A.card ≤ Sp.card := by
    rw [hBr, Finset.card_union_of_disjoint hdisj] at hr; omega
  obtain ⟨Q, hQSp, hQcard⟩ := Finset.exists_subset_card_eq hSp
  have hQne : Q.Nonempty := by rw [← Finset.card_pos]; omega
  obtain ⟨q, hq⟩ := hQne
  have hqr : G.dist v₀ q = r := by
    have := hQSp hq; simp only [Sp, Finset.mem_filter, Finset.mem_univ, true_and] at this; exact this
  have hdisjQ : Disjoint A Q := Finset.disjoint_of_subset_right hQSp hdisj
  have memS : ∀ v, v ∈ ((A ∪ Q : Finset (Fin n)) : Set (Fin n)) ↔ v ∈ A ∨ v ∈ Q := by
    intro v; simp
  have hle : ∀ v, v ∈ A ∨ v ∈ Q → G.dist v₀ v ≤ r := by
    intro v hv
    rcases hv with hv | hv
    · simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hv; omega
    · have := hQSp hv; simp only [Sp, Finset.mem_filter, Finset.mem_univ, true_and] at this; omega
  have hv₀S : v₀ ∈ A ∨ v₀ ∈ Q := by
    by_cases h0 : r = 0
    · right
      have : q = v₀ := by
        have := ((hconn q).dist_eq_zero_iff).mp (by omega); exact this.symm
      rw [← this]; exact hq
    · left; simp only [A, Finset.mem_filter, Finset.mem_univ, true_and, SimpleGraph.dist_self]; omega
  refine ⟨((A ∪ Q : Finset (Fin n)) : Set (Fin n)), r, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Set.ncard_coe_finset, Finset.card_union_of_disjoint hdisjQ]; omega
  · exact (memS v₀).mpr hv₀S
  · intro v hv
    rw [memS]
    by_cases h0 : r = 0
    · have : v = v₀ := (((hconn v).dist_eq_zero_iff).mp (by omega)).symm
      rw [this]; exact hv₀S
    · left; simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]; omega
  · intro v hv; exact hle v ((memS v).mp hv)
  · exact ⟨q, (memS q).mpr (Or.inr hq), hqr⟩
  · intro v hv hne
    obtain ⟨u, hu, hdu⟩ := h42_pred (hconn v) hne
    have hvr := hle v ((memS v).mp hv)
    refine ⟨u, (memS u).mpr (Or.inl ?_), hu, hdu⟩
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]; omega

theorem solution (n : ℕ) (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hn : 12 ≤ α * (n : ℝ)) (G : SimpleGraph (Fin n))
    (hG : CycleLengthsExp.WellSpread.IsAlphaExpander α G) :
    ∃ (S : Set (Fin n)) (T : G.Subgraph) (v₀ : Fin n) (m : ℕ),
      S.ncard = Nat.floor (α * (n : ℝ) / 4) ∧
      T.verts = S ∧
      v₀ ∈ S ∧
      T.spanningCoe.IsAcyclic ∧
      (∀ v ∈ S, T.spanningCoe.Reachable v₀ v) ∧
      (∀ v ∈ S, CycleLengthsExp.WellSpread.level T v₀ v ≤ m) ∧
      (∃ v ∈ S, CycleLengthsExp.WellSpread.level T v₀ v = m) ∧
      (∀ t ∈ S, ∀ q : Fin n, q ∉ S → G.Adj t q →
        m - 1 ≤ CycleLengthsExp.WellSpread.level T v₀ t) := by
  classical
  -- `n ≥ 1` from `α * n ≥ 12`.
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      norm_num at hn
    · exact h
  -- The expander hypothesis, unfolded once.
  have hG' : ∀ U : Set (Fin n), U.ncard ≤ (Fintype.card (Fin n) + 1) / 2 →
      α * (U.ncard : ℝ) ≤
        (CycleLengthsExp.WellSpread.extNbhd G U).ncard := hG
  rw [Fintype.card_fin] at hG'
  -- Connectivity: every vertex is reachable from any fixed v₀.
  -- Let U = reachable set from v₀. extNbhd(U) = ∅ (a neighbour of a
  -- reachable vertex is reachable), so if |U| ≤ (n+1)/2 expansion forces
  -- |U| = 0, contradicting v₀ ∈ U; hence |U| > (n+1)/2. The same
  -- argument on Uᶜ (whose external neighbourhood is also empty: a
  -- neighbour in U of a vertex of Uᶜ would make it reachable) forces
  -- |Uᶜ| = 0, so U = univ.
  have hconn : ∀ (v₀ : Fin n) (v : Fin n), G.Reachable v₀ v := by
    intro v₀ v
    set U : Set (Fin n) := {w | G.Reachable v₀ w} with hUdef
    have hU0 : v₀ ∈ U := SimpleGraph.Reachable.refl v₀
    have hUnbhd : CycleLengthsExp.WellSpread.extNbhd G U = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro z hz
      obtain ⟨hzU, u, hu, hAdj⟩ := hz
      exact hzU (hu.trans ⟨Walk.cons hAdj Walk.nil⟩)
    have hcompl_nbhd : CycleLengthsExp.WellSpread.extNbhd G Uᶜ = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro z hz
      obtain ⟨hzUc, u, hu, hAdj⟩ := hz
      -- z ∈ U (else z ∈ Uᶜ), u ∈ Uᶜ, Adj u z: then u is reachable via z.
      have hzU : z ∈ U := Set.notMem_compl_iff.mp hzUc
      have huU : u ∈ U := (hzU.trans ⟨Walk.cons hAdj.symm Walk.nil⟩)
      exact hu huU
    have hUcard : U.ncard + Uᶜ.ncard = n := by
      have h := Set.ncard_add_ncard_compl U (Set.toFinite U) (Set.toFinite Uᶜ)
      rw [Nat.card_eq_fintype_card, Fintype.card_fin] at h
      exact h
    have hUgt : (n + 1) / 2 < U.ncard := by
      by_contra hle
      rw [not_lt] at hle
      have hexp := hG' U hle
      rw [hUnbhd, Set.ncard_empty, Nat.cast_zero] at hexp
      have hpos : (0 : ℝ) < α * (U.ncard : ℝ) := by
        apply mul_pos hα0
        have h1 : 0 < U.ncard := Iff.mpr (Set.ncard_pos (s := U)) ⟨v₀, hU0⟩
        exact_mod_cast h1
      linarith
    have hcompl_le : Uᶜ.ncard ≤ (n + 1) / 2 := by omega
    have hexp2 := hG' Uᶜ hcompl_le
    rw [hcompl_nbhd, Set.ncard_empty, Nat.cast_zero] at hexp2
    have hcompl0 : Uᶜ.ncard = 0 := by
      by_contra hne
      have hpos : (0 : ℝ) < α * (Uᶜ.ncard : ℝ) := by
        apply mul_pos hα0
        exact_mod_cast Nat.pos_of_ne_zero hne
      linarith
    have hUuniv : U = Set.univ := by
      rw [← Set.compl_empty_iff, ← Set.ncard_eq_zero (Set.toFinite Uᶜ)]
      exact hcompl0
    have hUuniv : U = Set.univ := by
      rw [← Set.compl_empty_iff, ← Set.ncard_eq_zero (Set.toFinite Uᶜ)]
      exact hcompl0
    have hvmem : v ∈ U := by rw [hUuniv]; exact Set.mem_univ v
    exact hvmem
  -- The root and the target size.
  set v₀ : Fin n := ⟨0, hn0⟩ with hv₀def
  have hN1 : 1 ≤ Nat.floor (α * (n : ℝ) / 4) :=
    Nat.floor_pos.mpr (by linarith)
  have hNn : Nat.floor (α * (n : ℝ) / 4) ≤ n := by
    have h1 : ((Nat.floor (α * (n : ℝ) / 4) : ℕ) : ℝ) ≤ α * (n : ℝ) / 4 :=
      Nat.floor_le (by positivity)
    have h2 : α * (n : ℝ) / 4 ≤ (n : ℝ) := by
      have h3 : α * (n : ℝ) ≤ (n : ℝ) := by
        have h := mul_le_mul_of_nonneg_right hα1 (show (0 : ℝ) ≤ (n : ℝ) by positivity)
        simpa using h
      linarith
    exact_mod_cast le_trans h1 h2
  obtain ⟨S, r, hScard, hv₀S, hprefix, hSle, hSmax, hparent⟩ :=
    bfs_prefix_set_proved n G v₀ _ (fun v => hconn v₀ v) hN1 hNn
  have hreachS : ∀ v ∈ S, G.Reachable v₀ v := fun v _ => hconn v₀ v
  obtain ⟨T, hTverts, hTacyc, hTreach, hTdist⟩ :=
    bfs_parent_tree_proved G S v₀ hv₀S hreachS hparent
  -- Level = dist_T + 1 = dist_G + 1 on S.
  have hlev : ∀ v ∈ S, CycleLengthsExp.WellSpread.level T v₀ v = G.dist v₀ v + 1 := by
    intro v hv
    show T.spanningCoe.dist v₀ v + 1 = G.dist v₀ v + 1
    rw [hTdist v hv]
  refine ⟨S, T, v₀, r + 1, hScard, hTverts, hv₀S, hTacyc, hTreach, ?_, ?_, ?_⟩
  · intro v hv
    rw [hlev v hv]
    have := hSle v hv
    omega
  · obtain ⟨v, hv, hvr⟩ := hSmax
    exact ⟨v, hv, by rw [hlev v hv, hvr]⟩
  · intro t ht q hq hAdj
    rw [hlev t ht]
    -- If dist(t) ≤ r - 2 then dist(q) ≤ dist(t) + 1 ≤ r - 1, so q ∈ S
    -- by the prefix property — contradiction. Hence r ≤ dist(t) + 1.
    by_contra hlt
    rw [not_le] at hlt
    have hdistq : G.dist v₀ q ≤ G.dist v₀ t + 1 := by
      obtain ⟨p, hp⟩ := (hconn v₀ t).exists_walk_length_eq_dist
      have h := SimpleGraph.dist_le (p.concat hAdj)
      rw [Walk.length_concat, hp] at h
      exact h
    have hqS : q ∈ S := hprefix q (by omega)
    exact hq hqS

theorem bfs_tree_prefix (n : ℕ) (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hn : 12 ≤ α * (n : ℝ)) (G : SimpleGraph (Fin n))
    (hG : CycleLengthsExp.WellSpread.IsAlphaExpander α G) :
    ∃ (S : Set (Fin n)) (T : G.Subgraph) (v₀ : Fin n) (m : ℕ),
      S.ncard = Nat.floor (α * (n : ℝ) / 4) ∧
      T.verts = S ∧
      v₀ ∈ S ∧
      T.spanningCoe.IsAcyclic ∧
      (∀ v ∈ S, T.spanningCoe.Reachable v₀ v) ∧
      (∀ v ∈ S, CycleLengthsExp.WellSpread.level T v₀ v ≤ m) ∧
      (∃ v ∈ S, CycleLengthsExp.WellSpread.level T v₀ v = m) ∧
      (∀ t ∈ S, ∀ q : Fin n, q ∉ S → G.Adj t q →
        m - 1 ≤ CycleLengthsExp.WellSpread.level T v₀ t) :=
  solution n α hα0 hα1 hn G hG
