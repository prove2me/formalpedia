-- Prove2me | solution 2 for CycleLengthsExp.ManyLengths.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T07:10:49.140178+00:00
-- url     : https://prove2.me/submissions/e9deee5a-b0c9-40bc-9d4a-07fc5eb5eb10

import Mathlib
import Definitions.Def_CycleLengthsExp_ManyLengths_Setting
import Theorems.Thm_CycleLengthsExp_ManyLengths_bcr_branching
import Theorems.Thm_CycleLengthsExp_ManyLengths_path_after_deletion
import Theorems.Thm_CycleLengthsExp_ManyLengths_tree_extension_attach
import Theorems.Thm_CycleLengthsExp_ManyLengths_x0_large

-- carved verbatim out of submission 8c7f8aa2-73c1-42e7-8c03-0d16eb2f7c3d, lines 2778-2939

section
set_option autoImplicit false
open SimpleGraph CycleLengthsExp CycleLengthsExp.ManyLengths

theorem k_bound_proof : ∃ K : ℝ, 0 < K ∧ ∀ α : ℝ, 0 < α → α ≤ 1 →
    (kNum α : ℝ) ≤ K * Real.logb 2 (2 / α) / α := by
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨12 * Real.log 2 + 3, by linarith, fun α hα0 hα1 => ?_⟩
  have hαne : α ≠ 0 := ne_of_gt hα0
  have hlogne : Real.log 2 ≠ 0 := ne_of_gt hlog2
  -- (i) L := logb 2 (2/α) ≥ 1
  have hL1 : (1:ℝ) ≤ Real.logb 2 (2 / α) := by
    have h2 : (2:ℝ) ≤ 2 / α := by
      rw [le_div_iff₀ hα0]
      linarith [hα1]
    calc (1:ℝ) = Real.logb 2 2 := (Real.logb_self_eq_one (by norm_num)).symm
      _ ≤ Real.logb 2 (2 / α) :=
          Real.logb_le_logb_of_le (by norm_num) (by norm_num) h2
  -- (ii) numerator: logb 2 (3/α) ≤ 2 * logb 2 (2/α)
  have hnum : Real.logb 2 (3 / α) ≤ 2 * Real.logb 2 (2 / α) := by
    have h3α : (3:ℝ) / α ≤ (2 / α) ^ 2 := by
      have hαsq : (0:ℝ) < α ^ 2 := by positivity
      have e1 : (3:ℝ) / α = (3 * α) / (α ^ 2) := by
        field_simp
      have e2 : ((2:ℝ) / α) ^ 2 = 4 / (α ^ 2) := by
        field_simp
        ring
      rw [e1, e2, div_le_div_iff_of_pos_right hαsq]
      linarith [hα1]
    have h3αpos : (0:ℝ) < 3 / α := div_pos (by norm_num) hα0
    calc Real.logb 2 (3 / α) ≤ Real.logb 2 ((2 / α) ^ 2) :=
            Real.logb_le_logb_of_le (by norm_num) h3αpos h3α
      _ = 2 * Real.logb 2 (2 / α) := by
            simp only [Real.logb_pow, Nat.cast_ofNat]
  -- (iii) denominator: logb 2 (1+α/2) ≥ α / (3 * log 2)
  have hden : α / (3 * Real.log 2) ≤ Real.logb 2 (1 + α / 2) := by
    have hpos : (0:ℝ) < 1 + α / 2 := by linarith
    have h1ln : (α / 3 : ℝ) ≤ Real.log (1 + α / 2) := by
      have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
      rw [Real.log_inv] at h
      have h2 : (1:ℝ) - (1 + α / 2)⁻¹ ≤ Real.log (1 + α / 2) := by linarith
      have hne : ((1:ℝ) + α / 2) ≠ 0 := ne_of_gt hpos
      have e : (1:ℝ) - (1 + α / 2)⁻¹ = (α / 2) / (1 + α / 2) := by
        rw [inv_eq_one_div]
        field_simp
        ring
      have hα2 : α ^ 2 ≤ α := by
        have h := mul_le_mul_of_nonneg_left hα1 (le_of_lt hα0)
        rw [mul_one] at h
        have e2 : α ^ 2 = α * α := by ring
        rw [e2]; exact h
      have h3 : (α / 3 : ℝ) ≤ (α / 2) / (1 + α / 2) := by
        rw [le_div_iff₀ hpos]
        have e : (α / 3) * (1 + α / 2) = α / 2 - (α - α ^ 2) / 6 := by ring
        rw [e]
        have hnn : (0:ℝ) ≤ (α - α ^ 2) / 6 :=
          div_nonneg (by linarith [hα2]) (by norm_num)
        linarith
      rw [e] at h2
      exact h3.trans h2
    have hlogb_eq : Real.logb 2 (1 + α / 2)
        = Real.log (1 + α / 2) / Real.log 2 := rfl
    have h3' : (α / 3 : ℝ) / Real.log 2
        ≤ Real.log (1 + α / 2) / Real.log 2 :=
      (div_le_div_iff_of_pos_right hlog2).mpr h1ln
    have eα : α / (3 * Real.log 2) = (α / 3) / Real.log 2 := by ring
    rw [hlogb_eq, eα]
    exact h3'
  have hdenpos : (0:ℝ) < Real.logb 2 (1 + α / 2) := by
    have hα3 : (0:ℝ) < α / (3 * Real.log 2) :=
      div_pos hα0 (mul_pos (by norm_num) hlog2)
    exact lt_of_lt_of_le hα3 hden
  -- (iv) the ratio A := logb 2 (3/α) / logb 2 (1+α/2) ≤ 6 * log 2 * L / α
  have hA : Real.logb 2 (3 / α) / Real.logb 2 (1 + α / 2)
      ≤ 6 * Real.log 2 * Real.logb 2 (2 / α) / α := by
    rw [div_le_iff₀ hdenpos]
    have hnn : (0:ℝ) ≤ 6 * Real.log 2 * Real.logb 2 (2 / α) / α :=
      div_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) (le_of_lt hlog2))
          (le_trans (by norm_num) hL1)) (le_of_lt hα0)
    have hmul := mul_le_mul_of_nonneg_left hden hnn
    have h3logne : (3:ℝ) * Real.log 2 ≠ 0 := mul_ne_zero (by norm_num) hlogne
    have eR : (6 * Real.log 2 * Real.logb 2 (2 / α) / α) * (α / (3 * Real.log 2))
        = 2 * Real.logb 2 (2 / α) := by
      field_simp
      ring
    rw [eR] at hmul
    calc Real.logb 2 (3 / α) ≤ 2 * Real.logb 2 (2 / α) := hnum
      _ ≤ (6 * Real.log 2 * Real.logb 2 (2 / α) / α)
          * Real.logb 2 (1 + α / 2) := hmul
  -- (v) ceil: ↑⌈A⌉₊ ≤ A + 1
  have hA0 : (0:ℝ) ≤ Real.logb 2 (3 / α) / Real.logb 2 (1 + α / 2) :=
    div_nonneg
      (Real.logb_nonneg (by norm_num) (by
        rw [le_div_iff₀ hα0]
        linarith [hα1]))
      (le_of_lt hdenpos)
  have hceil : ((Nat.ceil (Real.logb 2 (3 / α) / Real.logb 2 (1 + α / 2)) : ℕ) : ℝ)
      ≤ Real.logb 2 (3 / α) / Real.logb 2 (1 + α / 2) + 1 :=
    (Nat.ceil_lt_add_one hA0).le
  -- (vi) absorb the +3 via logb 2 (2/α) / α ≥ 1
  have hM : (1:ℝ) ≤ Real.logb 2 (2 / α) / α := by
    rw [le_div_iff₀ hα0]
    linarith [hL1, hα1]
  -- assembly
  unfold kNum
  push_cast
  have step1 : (2 * ((Nat.ceil (Real.logb 2 (3 / α) / Real.logb 2 (1 + α / 2)) : ℕ) : ℝ) + 1)
      ≤ 2 * (Real.logb 2 (3 / α) / Real.logb 2 (1 + α / 2)) + 3 := by
    have h1 := mul_le_mul_of_nonneg_left hceil (by norm_num : (0:ℝ) ≤ 2)
    linarith
  have step2 : (2 * (Real.logb 2 (3 / α) / Real.logb 2 (1 + α / 2)) + 3)
      ≤ 2 * (6 * Real.log 2 * Real.logb 2 (2 / α) / α) + 3 := by
    have h2 := mul_le_mul_of_nonneg_left hA (by norm_num : (0:ℝ) ≤ 2)
    linarith
  have step3 : (2 * (6 * Real.log 2 * Real.logb 2 (2 / α) / α) + 3)
      ≤ (12 * Real.log 2 + 3) * (Real.logb 2 (2 / α) / α) := by
    have h3M : (3:ℝ) ≤ 3 * (Real.logb 2 (2 / α) / α) := by linarith [hM]
    have e2 : (12 * Real.log 2 + 3) * (Real.logb 2 (2 / α) / α)
        = 12 * Real.log 2 * (Real.logb 2 (2 / α) / α)
          + 3 * (Real.logb 2 (2 / α) / α) := by ring
    rw [e2]
    have key : (2:ℝ) * (6 * Real.log 2 * Real.logb 2 (2 / α) / α) + 3
        ≤ 12 * Real.log 2 * (Real.logb 2 (2 / α) / α)
          + 3 * (Real.logb 2 (2 / α) / α) := by
      have ering : (2:ℝ) * (6 * Real.log 2 * Real.logb 2 (2 / α) / α)
          = 12 * Real.log 2 * (Real.logb 2 (2 / α) / α) := by ring
      rw [ering]
      have hle := add_le_add_right h3M
        (12 * Real.log 2 * (Real.logb 2 (2 / α) / α))
      linarith
    exact key
  calc (2 * ((Nat.ceil (Real.logb 2 (3 / α) / Real.logb 2 (1 + α / 2)) : ℕ) : ℝ) + 1)
        ≤ 2 * (Real.logb 2 (3 / α) / Real.logb 2 (1 + α / 2)) + 3 := step1
      _ ≤ 2 * (6 * Real.log 2 * Real.logb 2 (2 / α) / α) + 3 := step2
      _ ≤ (12 * Real.log 2 + 3) * (Real.logb 2 (2 / α) / α) := step3
      _ = (12 * Real.log 2 + 3) * Real.logb 2 (2 / α) / α := by ring

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

theorem bfs_tree_prefix_proof (n : ℕ) (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1)
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

theorem cl_prefix_mem {α : Type*} [DecidableEq α] {l₁ l₂ : List α} (hp : l₁ <+: l₂) {a : α}
    (ha : a ∈ l₂) (hlt : l₂.idxOf a < l₁.length) : a ∈ l₁ ∧ l₁.idxOf a = l₂.idxOf a := by
  obtain ⟨t, rfl⟩ := hp
  by_cases h : a ∈ l₁
  · exact ⟨h, (List.idxOf_append_of_mem h).symm⟩
  · rw [List.idxOf_append_of_notMem h] at hlt; omega

theorem cl_seg {n : ℕ} {G : SimpleGraph (Fin n)} {u v : Fin n} (P : G.Walk u v) (hP : P.IsPath)
    (a b : Fin n) (ha : a ∈ P.support) (hb : b ∈ P.support)
    (hab : P.support.idxOf a ≤ P.support.idxOf b) :
    ∃ W : G.Walk a b, W.IsPath ∧ W.support ⊆ P.support ∧
      W.length = P.support.idxOf b - P.support.idxOf a := by
  have hpre := P.support_takeUntil_prefix_support hb
  have hlen : (P.takeUntil b hb).support.length = P.support.idxOf b + 1 := by
    rw [SimpleGraph.Walk.length_support, SimpleGraph.Walk.length_takeUntil]
  obtain ⟨ha', hidx⟩ := cl_prefix_mem hpre ha (by omega)
  refine ⟨(P.takeUntil b hb).dropUntil a ha', (hP.takeUntil hb).dropUntil ha', ?_, ?_⟩
  · intro x hx
    exact P.support_takeUntil_subset hb ((P.takeUntil b hb).support_dropUntil_subset ha' hx)
  · rw [SimpleGraph.Walk.length_dropUntil, SimpleGraph.Walk.length_takeUntil, hidx]

theorem h42c_ne_head {n : ℕ} {G : SimpleGraph (Fin n)} {u v x : Fin n} (p : G.Walk u v) (hp : p.IsPath)
    (hx : x ∈ p.support.tail) : x ≠ u := by
  have h := hp.support_nodup
  rw [SimpleGraph.Walk.support_eq_cons] at h
  intro hxu; subst hxu; exact (List.nodup_cons.mp h).1 hx

theorem h42c_cycle {n : ℕ} {G : SimpleGraph (Fin n)} {w w₀ : Fin n} (hne : w ≠ w₀)
    (leg : G.Walk w w₀) (seg : G.Walk w₀ w) (hl : leg.IsPath) (hs : seg.IsPath)
    (h2 : 2 ≤ leg.length)
    (hdisj : ∀ a ∈ leg.support.tail, ∀ b ∈ seg.support.tail, a ≠ b) : (leg.append seg).IsCycle := by
  rw [SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length]
  have hnn : ¬ (leg.append seg).Nil := by
    intro h; have := SimpleGraph.Walk.Nil.length_eq_zero h  
    rw [SimpleGraph.Walk.length_append] at this; omega
  have hseg1 : seg.length ≠ 0 := by
    intro h0; exact hne (SimpleGraph.Walk.eq_of_length_eq_zero h0).symm
  constructor
  · rw [SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_tail_of_not_nil _ hnn,
      SimpleGraph.Walk.support_append, SimpleGraph.Walk.support_eq_cons leg, List.cons_append,
      List.tail_cons]
    rw [List.nodup_append]
    refine ⟨?_, ?_, hdisj⟩
    · exact hl.support_nodup.sublist (List.tail_sublist _)
    · exact hs.support_nodup.sublist (List.tail_sublist _)
  · rw [SimpleGraph.Walk.length_append]; omega

theorem branch_cycles_repaired_proof (n : ℕ) (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (G : SimpleGraph (Fin n))
    (hG : CycleLengthsExp.WellSpread.IsAlphaExpander α G)
    (S : Set (Fin n)) (T : G.Subgraph) (v₀ : Fin n) (m : ℕ)
    (hScard : S.ncard = Nat.floor (α * (n : ℝ) / 4))
    (hTverts : T.verts = S)
    (hv₀ : v₀ ∈ S)
    (hTacyc : T.spanningCoe.IsAcyclic)
    (hTreach : ∀ v ∈ S, T.spanningCoe.Reachable v₀ v)
    (hTlev : ∀ v ∈ S, CycleLengthsExp.WellSpread.level T v₀ v ≤ m)
    (hTmax : ∃ v ∈ S, CycleLengthsExp.WellSpread.level T v₀ v = m)
    (hTfront : ∀ t ∈ S, ∀ q : Fin n, q ∉ S → G.Adj t q →
      m - 1 ≤ CycleLengthsExp.WellSpread.level T v₀ t)
    (u v : Fin n) (P : G.Walk u v) (hPpath : P.IsPath)
    (hPlen : P.length = Nat.ceil (α * (n : ℝ) / 4) - 1)
    (hPdisj : ∀ w ∈ P.support, w ∉ S)
    (T₁ : G.Subgraph) (M₁ : ℕ) (X₁ : Set (Fin n)) (j : ℕ)
    (hText : T.verts ⊆ T₁.verts ∧
      (∀ a b : Fin n, T.spanningCoe.Adj a b → T₁.spanningCoe.Adj a b))
    (hT₁acyc : T₁.spanningCoe.IsAcyclic)
    (hT₁reach : ∀ w ∈ T₁.verts, T₁.spanningCoe.Reachable v₀ w)
    (hT₁lev : ∀ w ∈ T₁.verts, CycleLengthsExp.WellSpread.level T₁ v₀ w ≤ M₁)
    (hT₁max : ∃ w ∈ T₁.verts, CycleLengthsExp.WellSpread.level T₁ v₀ w = M₁)
    (hT₁avoid : ∀ w ∈ T₁.verts, w ∉ P.support)
    (hX₁sub : X₁ ⊆ CycleLengthsExp.ManyLengths.X0 α G S P)
    (hX₁card : ((CycleLengthsExp.ManyLengths.X0 α G S P).ncard : ℝ) /
        ((CycleLengthsExp.ManyLengths.kNum α : ℝ) + 1) ≤ (X₁.ncard : ℝ))
    (hX₁card2 : 2 ≤ X₁.ncard)
    (hattach : ∀ x ∈ X₁, ∃ y ∈ T₁.verts,
      CycleLengthsExp.WellSpread.level T₁ v₀ y = j ∧ G.Adj x y) :
    ∃ (X₃ : Set (Fin n)) (A : ℕ) (segLen : Fin n → ℕ),
      X₃ ⊆ X₁ ∧
      (X₁.ncard : ℝ) / 4 ≤ (X₃.ncard : ℝ) ∧
      (∀ w ∈ X₃, ∃ cyc : G.Walk w w, cyc.IsCycle ∧ cyc.length = A + segLen w) ∧
      Set.InjOn segLen X₃ := by
  classical
  have hX₁T₁ : ∀ x ∈ X₁, x ∉ T₁.verts := fun x hx hxT => hT₁avoid x hxT (hX₁sub hx).1
  have hv₀T₁ : v₀ ∈ T₁.verts := hText.1 (hTverts ▸ hv₀)
  choose yy hyy using hattach
  obtain ⟨d, Y, w₀, hYX, hw₀Y, hYcard, hlegs⟩ :=
    CycleLengthsExp.ManyLengths.bcr_branching n G T₁ v₀ X₁ j yy hT₁acyc hT₁reach hv₀T₁ hX₁T₁ hyy hX₁card2
  have hw₀X : w₀ ∈ X₁ := hYX hw₀Y
  have hPs : ∀ x ∈ X₁, x ∈ P.support := fun x hx => (hX₁sub hx).1
  have hseg : ∀ a b, a ∈ P.support → b ∈ P.support → ∃ W : G.Walk a b, W.IsPath ∧
      W.support ⊆ P.support ∧
      W.length = (if P.support.idxOf a ≤ P.support.idxOf b then
          P.support.idxOf b - P.support.idxOf a else
          P.support.idxOf a - P.support.idxOf b) := by
    intro a b ha hb
    by_cases h : P.support.idxOf a ≤ P.support.idxOf b
    · obtain ⟨W, h1, h2, h3⟩ := cl_seg P hPpath a b ha hb h
      exact ⟨W, h1, h2, by rw [if_pos h, h3]⟩
    · obtain ⟨W, h1, h2, h3⟩ := cl_seg P hPpath b a hb ha (by omega)
      refine ⟨W.reverse, h1.reverse, by rw [SimpleGraph.Walk.support_reverse]; intro x hx; exact h2 (List.mem_reverse.mp hx), ?_⟩
      rw [if_neg h, SimpleGraph.Walk.length_reverse, h3]
  let idx : Fin n → ℕ := fun x => P.support.idxOf x
  let segLen : Fin n → ℕ := fun w => if idx w₀ ≤ idx w then idx w - idx w₀ else idx w₀ - idx w
  have hcyc : ∀ w, w ∈ X₁ → w ∉ Y → ∃ cyc : G.Walk w w, cyc.IsCycle ∧ cyc.length = (2 * d + 2) + segLen w := by
    intro w hw hwY
    have hne : w ≠ w₀ := fun h => hwY (h ▸ hw₀Y)
    obtain ⟨leg, hlp, hll, hls⟩ := hlegs w ⟨hw, hwY⟩
    obtain ⟨seg, hsp, hss, hsl⟩ := hseg w₀ w (hPs w₀ hw₀X) (hPs w hw)
    refine ⟨leg.append seg, h42c_cycle hne leg seg hlp hsp (by omega) ?_, ?_⟩
    · intro a ha b hb hab
      subst hab
      have h1 := h42c_ne_head leg hlp ha
      have h2 := h42c_ne_head seg hsp hb
      have h3 : a ∈ P.support := hss (List.mem_of_mem_tail hb)
      rcases hls a (List.mem_of_mem_tail ha) with h | h | h
      · exact h1 h
      · exact h2 h
      · exact hT₁avoid a h h3
    · rw [SimpleGraph.Walk.length_append, hll, hsl]
  have hidx_inj : ∀ a ∈ X₁, ∀ b ∈ X₁, idx a = idx b → a = b := fun a ha b _ h =>
    (List.idxOf_inj (hPs a ha)).mp h
  let X₂ : Set (Fin n) := X₁ \ Y
  let Lft : Set (Fin n) := {w | w ∈ X₂ ∧ idx w < idx w₀}
  let Rgt : Set (Fin n) := {w | w ∈ X₂ ∧ idx w₀ < idx w}
  have hsplit : X₂ ⊆ Lft ∪ Rgt := by
    intro w hw
    have hne : w ≠ w₀ := fun h => hw.2 (h ▸ hw₀Y)
    have hne' : idx w ≠ idx w₀ := fun h => hne (hidx_inj w hw.1 w₀ hw₀X h)
    rcases Nat.lt_or_gt_of_ne hne' with h | h
    · exact Or.inl ⟨hw, h⟩
    · exact Or.inr ⟨hw, h⟩
  have hc1 : X₂.ncard ≤ Lft.ncard + Rgt.ncard :=
    (Set.ncard_le_ncard hsplit (Set.toFinite _)).trans (Set.ncard_union_le _ _)
  have hc2 : X₂.ncard + Y.ncard = X₁.ncard := Set.ncard_diff_add_ncard_of_subset hYX (Set.toFinite _)
  have hc3 : 2 * Y.ncard ≤ X₁.ncard := by
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 2)] at hYcard
    have : (Y.ncard * 2 : ℕ) ≤ X₁.ncard := by exact_mod_cast hYcard
    omega
  have hfin : ∀ X₃ : Set (Fin n), X₃ ⊆ X₂ → X₁.ncard ≤ X₃.ncard * 4 → Set.InjOn segLen X₃ →
      ∃ (X₃ : Set (Fin n)) (A : ℕ) (segLen : Fin n → ℕ),
      X₃ ⊆ X₁ ∧ (X₁.ncard : ℝ) / 4 ≤ (X₃.ncard : ℝ) ∧
      (∀ w ∈ X₃, ∃ cyc : G.Walk w w, cyc.IsCycle ∧ cyc.length = A + segLen w) ∧
      Set.InjOn segLen X₃ := by
    intro X₃ hX₃ hcard hinj
    refine ⟨X₃, 2 * d + 2, segLen, fun w hw => (hX₃ hw).1, ?_, fun w hw => hcyc w (hX₃ hw).1 (hX₃ hw).2, hinj⟩
    rw [div_le_iff₀ (by norm_num : (0:ℝ) < 4)]
    exact_mod_cast hcard
  by_cases hcmp : Lft.ncard ≤ Rgt.ncard
  · refine hfin Rgt (fun w hw => hw.1) (by omega) ?_
    intro a ha b hb hab
    have h1 := ha.2; have h2 := hb.2
    simp only [segLen] at hab
    rw [if_pos h1.le, if_pos h2.le] at hab
    exact hidx_inj a ha.1.1 b hb.1.1 (by omega)
  · refine hfin Lft (fun w hw => hw.1) (by omega) ?_
    intro a ha b hb hab
    have h1 := ha.2; have h2 := hb.2
    simp only [segLen] at hab
    rw [if_neg (by omega), if_neg (by omega)] at hab
    exact hidx_inj a ha.1.1 b hb.1.1 (by omega)

theorem solution : ∃ c : ℝ, 0 < c ∧ ∀ α : ℝ, 0 < α → α ≤ 1 →
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ G : SimpleGraph (Fin n),
      CycleLengthsExp.WellSpread.IsAlphaExpander α G →
        c * (α ^ 3 / Real.logb 2 (2 / α)) * (n : ℝ) ≤
          ((CycleLengthsExp.WellSpread.cycleLengths G).ncard : ℝ) := by
  obtain ⟨K, hK0, hK⟩ := k_bound_proof
  refine ⟨1 / (48 * (K + 1)), by positivity, fun α hα0 hα1 => ?_⟩
  refine ⟨Nat.ceil (12 / α) + Nat.ceil (24 * (K + 1) * Real.logb 2 (2 / α) / α ^ 3) + 1, fun n hn G hG => ?_⟩
  -- `n ≥ 1` and `12 ≤ α * n` from `n ≥ ⌈12/α⌉₊ + 1`.
  have hn1 : 1 ≤ n := by omega
  have hαn : (12 : ℝ) ≤ α * (n : ℝ) := by
    have h1 : (12 : ℝ) / α ≤ (Nat.ceil (12 / α) : ℝ) := Nat.le_ceil _
    have h2 : ((Nat.ceil (12 / α) : ℝ)) + 1 ≤ (n : ℝ) := by
      have hnA : Nat.ceil (12 / α) + 1 ≤ n := by omega
      exact_mod_cast hnA
    have h3 : (12 : ℝ) / α < (n : ℝ) := by linarith
    rw [div_lt_iff₀ hα0] at h3
    rw [mul_comm] at h3
    linarith
  -- BFS tree prefix (NEW NODE 1).
  obtain ⟨S, T, v₀, m, hScard, hTverts, hv₀, hTacyc, hTreach, hTlev, hTmax, hTfront⟩ :=
    bfs_tree_prefix_proof n α hα0 hα1 hαn G hG
  -- Long path `P` in `G ∖ S` (proved child).
  obtain ⟨u, v, P, hPpath, hPlen, hPdisj⟩ :=
    CycleLengthsExp.ManyLengths.path_after_deletion n (by omega) α hα0 hα1 G hG S hScard
  -- `|X₀| ≥ α²n/12` (proved child).
  have hX0 := CycleLengthsExp.ManyLengths.x0_large n α hα0 hα1 hαn G hG S hScard u v P hPpath hPlen hPdisj
  -- Tree extension + attachment pigeonhole (NEW NODE 2).
  obtain ⟨T₁, M₁, X₁, j, hText, hT₁acyc, hT₁reach, hT₁lev, hT₁max, hT₁avoid,
    hX₁sub, hX₁card, hattach⟩ :=
    CycleLengthsExp.ManyLengths.tree_extension_attach n α hα0 hα1 G hG S T v₀ m hScard hTverts hv₀ hTacyc
      hTreach hTlev hTmax hTfront u v P hPpath hPlen hPdisj
  -- Real facts moved up: needed to discharge `2 ≤ X₁.ncard` for the repaired node.
  have hL1 : (1 : ℝ) ≤ Real.logb 2 (2 / α) := by
    have h2 : (2 : ℝ) ≤ 2 / α := by
      rw [le_div_iff₀ hα0]
      linarith [hα1]
    calc (1 : ℝ) = Real.logb 2 2 := (Real.logb_self_eq_one (by norm_num)).symm
      _ ≤ Real.logb 2 (2 / α) :=
        Real.logb_le_logb_of_le (show (1 : ℝ) < 2 by norm_num)
          (show (0 : ℝ) < 2 by norm_num) h2
  have hLpos : (0 : ℝ) < Real.logb 2 (2 / α) := by linarith [hL1]
  have hLne : Real.logb 2 (2 / α) ≠ 0 := ne_of_gt hLpos
  have hαne : α ≠ 0 := ne_of_gt hα0
  have hK1pos : (0 : ℝ) < K + 1 := by linarith [hK0]
  have hK1ne : K + 1 ≠ 0 := ne_of_gt hK1pos
  have hLα : (1 : ℝ) ≤ Real.logb 2 (2 / α) / α := by
    rw [le_div_iff₀ hα0]
    calc (1 : ℝ) * α = α := one_mul _
      _ ≤ 1 := hα1
      _ ≤ Real.logb 2 (2 / α) := hL1
  have hk1 : (CycleLengthsExp.ManyLengths.kNum α : ℝ) + 1 ≤
      (K + 1) * Real.logb 2 (2 / α) / α := by
    have hk := hK α hα0 hα1
    calc (CycleLengthsExp.ManyLengths.kNum α : ℝ) + 1
        ≤ K * Real.logb 2 (2 / α) / α + Real.logb 2 (2 / α) / α := by linarith
      _ = (K + 1) * Real.logb 2 (2 / α) / α := by ring
  have hk1pos : (0 : ℝ) < (CycleLengthsExp.ManyLengths.kNum α : ℝ) + 1 := by positivity
  -- Discharge `2 ≤ X₁.ncard`: |X₀|/(k+1) ≥ 2 via n ≥ 24(K+1)L/α³.
  have hn_big : (24 * (K + 1) * Real.logb 2 (2 / α) / α ^ 3 : ℝ) ≤ (n : ℝ) := by
    have h1 : (24 * (K + 1) * Real.logb 2 (2 / α) / α ^ 3 : ℝ) ≤
        (Nat.ceil (24 * (K + 1) * Real.logb 2 (2 / α) / α ^ 3) : ℝ) := Nat.le_ceil _
    have h2 : (Nat.ceil (24 * (K + 1) * Real.logb 2 (2 / α) / α ^ 3) : ℝ) ≤ (n : ℝ) := by
      have hnB : Nat.ceil (24 * (K + 1) * Real.logb 2 (2 / α) / α ^ 3) ≤ n := by omega
      exact_mod_cast hnB
    linarith
  have hα3 : (24 : ℝ) * (K + 1) * Real.logb 2 (2 / α) ≤ α ^ 3 * (n : ℝ) := by
    have hα3pos : (0 : ℝ) < α ^ 3 := by positivity
    rw [div_le_iff₀ hα3pos] at hn_big
    linarith [hn_big]
  have hkey : (2 : ℝ) * ((K + 1) * Real.logb 2 (2 / α) / α) ≤ α ^ 2 * (n : ℝ) / 12 := by
    have h1 : (2 : ℝ) * ((K + 1) * Real.logb 2 (2 / α) / α) =
        (24 * (K + 1) * Real.logb 2 (2 / α)) / (12 * α) := by
      field_simp
      ring
    rw [h1, div_le_div_iff₀ (by positivity : (0 : ℝ) < 12 * α) (by norm_num : (0 : ℝ) < 12)]
    nlinarith [hα3]
  have hX0div : (2 : ℝ) ≤ ((CycleLengthsExp.ManyLengths.X0 α G S P).ncard : ℝ) /
      ((CycleLengthsExp.ManyLengths.kNum α : ℝ) + 1) := by
    rw [le_div_iff₀ hk1pos]
    calc (2 : ℝ) * ((CycleLengthsExp.ManyLengths.kNum α : ℝ) + 1)
        ≤ 2 * ((K + 1) * Real.logb 2 (2 / α) / α) :=
          mul_le_mul_of_nonneg_left hk1 (by norm_num)
      _ ≤ α ^ 2 * (n : ℝ) / 12 := hkey
      _ ≤ ((CycleLengthsExp.ManyLengths.X0 α G S P).ncard : ℝ) := hX0
  have hX₁card2 : 2 ≤ X₁.ncard := by
    have h : (2 : ℝ) ≤ (X₁.ncard : ℝ) := le_trans hX0div hX₁card
    exact_mod_cast h
  -- Branching + cycles (NEW NODE 3).
  obtain ⟨X₃, A, segLen, hX₃sub, hX₃card, hcyc, hinj⟩ :=
    branch_cycles_repaired_proof n α hα0 hα1 G hG S T v₀ m hScard hTverts hv₀ hTacyc
      hTreach hTlev hTmax hTfront u v P hPpath hPlen hPdisj
      T₁ M₁ X₁ j hText hT₁acyc hT₁reach hT₁lev hT₁max hT₁avoid hX₁sub hX₁card hX₁card2 hattach
  -- Counting: the cycle lengths `A + segLen w`, `w ∈ X₃`, are distinct
  -- members of `cycleLengths G`, so `|X₃| ≤ |cycleLengths G|`.
  have himg : (fun w => A + segLen w) '' X₃ ⊆
      CycleLengthsExp.WellSpread.cycleLengths G := by
    rintro ℓ ⟨w, hw, rfl⟩
    obtain ⟨cyc, hcyc', hlen⟩ := hcyc w hw
    exact ⟨w, cyc, hcyc', hlen⟩
  have hinj' : Set.InjOn (fun w => A + segLen w) X₃ := by
    intro a ha b hb h
    exact hinj ha hb (Nat.add_left_cancel h)
  have himgcard : ((fun w => A + segLen w) '' X₃).ncard = X₃.ncard :=
    hinj'.ncard_image
  -- `cycleLengths G` is finite: a cycle has length `≤ n`.
  have hfin : (CycleLengthsExp.WellSpread.cycleLengths G).Finite := by
    apply Set.Finite.subset (Set.finite_le_nat n)
    rintro ℓ ⟨w, p, hp, rfl⟩
    have hnod := hp.support_nodup
    have h1 : p.support.tail.toFinset.card ≤ Finset.univ.card := Finset.card_le_univ _
    rw [List.toFinset_card_of_nodup hnod, Finset.card_univ, Fintype.card_fin] at h1
    have h2 : p.support.tail.length = p.support.length - 1 := List.length_tail
    have h3 : p.support.length = p.length + 1 := p.length_support
    simp only [Set.mem_ofPred_eq]
    omega
  have hle1 : X₃.ncard ≤ (CycleLengthsExp.WellSpread.cycleLengths G).ncard := by
    rw [← himgcard]
    exact Set.ncard_le_ncard himg hfin
  have hle1R : (X₃.ncard : ℝ) ≤
      ((CycleLengthsExp.WellSpread.cycleLengths G).ncard : ℝ) := by
    exact_mod_cast hle1
  -- Real arithmetic: `|X₃| ≥ α²n / (48(k+1))` and `k+1 ≤ (K+1)·L/α`.
  have hX3 : α ^ 2 * (n : ℝ) / (48 * ((CycleLengthsExp.ManyLengths.kNum α : ℝ) + 1)) ≤
      (X₃.ncard : ℝ) := by
    have hC : ((CycleLengthsExp.ManyLengths.X0 α G S P).ncard : ℝ) /
        (((CycleLengthsExp.ManyLengths.kNum α : ℝ) + 1) * 4) ≤ (X₃.ncard : ℝ) := by
      have h1 := div_le_div_of_nonneg_right hX₁card (show (0 : ℝ) ≤ 4 by norm_num)
      rw [div_div] at h1
      linarith [hX₃card]
    have hD : α ^ 2 * (n : ℝ) / 12 /
        (((CycleLengthsExp.ManyLengths.kNum α : ℝ) + 1) * 4) ≤
        ((CycleLengthsExp.ManyLengths.X0 α G S P).ncard : ℝ) /
          (((CycleLengthsExp.ManyLengths.kNum α : ℝ) + 1) * 4) :=
      div_le_div_of_nonneg_right hX0 (by positivity)
    have heq : α ^ 2 * (n : ℝ) / 12 /
        (((CycleLengthsExp.ManyLengths.kNum α : ℝ) + 1) * 4) =
        α ^ 2 * (n : ℝ) / (48 * ((CycleLengthsExp.ManyLengths.kNum α : ℝ) + 1)) := by
      rw [div_div]
      congr 1
      ring
    rw [heq] at hD
    linarith [hC, hD]
  -- Real arithmetic: `|X₃| ≥ α²n / (48(k+1))` and `k+1 ≤ (K+1)·L/α`.
  -- (Flattened to solution level: nested `have`s inside the old `hgoal`
  -- block repeatedly broke the parser in elab rounds 1–3.)
  have heq2 : (1 / (48 * (K + 1))) * (α ^ 3 / Real.logb 2 (2 / α)) * (n : ℝ) =
      α ^ 2 * (n : ℝ) / (48 * ((K + 1) * Real.logb 2 (2 / α) / α)) := by
    field_simp
  have hcmp2 : α ^ 2 * (n : ℝ) / (48 * ((K + 1) * Real.logb 2 (2 / α) / α)) ≤
      α ^ 2 * (n : ℝ) / (48 * ((CycleLengthsExp.ManyLengths.kNum α : ℝ) + 1)) := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact mul_le_mul_of_nonneg_left hk1 (show (0 : ℝ) ≤ 48 by norm_num)
  have hgoal : (1 / (48 * (K + 1))) * (α ^ 3 / Real.logb 2 (2 / α)) * (n : ℝ) ≤
      (X₃.ncard : ℝ) :=
    le_trans (le_trans heq2.le hcmp2) hX3
  linarith [hgoal, hle1R]

end
