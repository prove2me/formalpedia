-- Prove2me | solution 1 for CycleLengthsExp.ManyLengths.branch_cycles_repaired
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T23:51:19.573801+00:00
-- url     : https://prove2.me/submissions/00ff755f-edc2-4e16-b222-83bce12d7371

import Mathlib
import Definitions.Def_CycleLengthsExp_ManyLengths_Setting

open CycleLengthsExp CycleLengthsExp.ManyLengths
/-- REPAIRED 2026-10-18: the original `branch_cycles` (6f2911cf) is FALSE as stated
(pendant-vertex counterexample with X₁ = {0}; see `branch_cycles_counterexample.md`).
This version adds the hypothesis `hX₁card2 : 2 ≤ X₁.ncard`, which the paper's
pair-cycle argument needs (with |X₁| ≥ 2, both branching cases give |X₃| ≥ |X₁|/4
with genuine cycles; with |X₁| = 1 the conclusion can force a cycle at a degree-1
vertex, which does not exist). The assembly must discharge `2 ≤ X₁.ncard` by
raising n₀ (see triage report). Branching + cycles (Friedman–Krivelevich, p. 14: "Let T₂ be the tree
obtained by connecting each vertex in X₁ to one of its neighbors in the last
level of T₁. Let T₃ be the minimal subtree of T₂ containing X₁ and let v be
its root ... One of the branches contains at most half of the vertices of X₁,
denote this set by Y and let X₂ = X₁ ∖ Y ... at least half of the vertices of
X₂ appear on P on the same side of u ... Finally we construct a cycle C_w for
every w ∈ X₃ ... As the lengths of the cycles {C_w} are all distinct ...").

Why the lengths are distinct: every `w ∈ X₁` is a leaf of `T₂` attached to a
level-`j` vertex, so `dist_{T₃}(w, v) = j - depth(v)` is CONSTANT over
`w ∈ X₁`; `C_w` has length `dist(v,u) + dist_P(u,w) + dist_{T₃}(w,v) =
A + dist_P(u,w)` with `A` independent of `w`, and `w ↦ dist_P(u,w)` is
injective on `X₃` because all of `X₃` lies on the same side of `u` along the
path `P`. The statement packages exactly what the assembly consumes: the
cycles, the constant `A`, an injective length function `segLen`, and the
`|X₃| ≥ |X₁|/4` count. The `T₂`/`T₃`/branching machinery is internal to this
node's proof. This node is the last of the three-node decomposition of
`CycleLengthsExp.ManyLengths.theorem_2` (parent, Open): it consumes the
extended tree `T₁`, the set `X₁` and the level `j` of `tree_extension_attach`,
and its output (X₃, A, segLen) is exactly what the assembly counts to get
`Ω(α³/log(1/α))n` distinct cycle lengths. -/
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

theorem h42b_up {V : Type*} {G : SimpleGraph V} (par : V → V) (z : V) : ∀ t : ℕ,
    (∀ s < t, G.Adj (par^[s] z) (par^[s+1] z)) →
    ∃ q : G.Walk z (par^[t] z), q.length = t ∧
      q.support = (List.range (t+1)).map (fun s => par^[s] z) := by
  intro t
  induction t with
  | zero => intro _; exact ⟨SimpleGraph.Walk.nil, rfl, by simp⟩
  | succ t ih =>
    intro hadj
    obtain ⟨q, hq1, hq2⟩ := ih (fun s hs => hadj s (by omega))
    refine ⟨q.concat (hadj t (by omega)), ?_, ?_⟩
    · rw [SimpleGraph.Walk.length_concat, hq1]
    · rw [SimpleGraph.Walk.support_concat, hq2, List.range_succ (n := t + 1),
        List.map_append]
      rfl

theorem h42_branching (n : ℕ) (G : SimpleGraph (Fin n))
    (T₁ : G.Subgraph) (v₀ : Fin n) (X₁ : Set (Fin n)) (j : ℕ)
    (y : ∀ (x : Fin n), x ∈ X₁ → Fin n)
    (hT₁acyc : T₁.spanningCoe.IsAcyclic)
    (hT₁reach : ∀ w ∈ T₁.verts, T₁.spanningCoe.Reachable v₀ w)
    (hv₀ : v₀ ∈ T₁.verts)
    (hX₁T₁ : ∀ x ∈ X₁, x ∉ T₁.verts)
    (hy : ∀ (x : Fin n) (hx : x ∈ X₁), y x hx ∈ T₁.verts ∧
      CycleLengthsExp.WellSpread.level T₁ v₀ (y x hx) = j ∧ G.Adj x (y x hx))
    (hX₁card2 : 2 ≤ X₁.ncard) :
    ∃ (d : ℕ) (Y : Set (Fin n)) (w₀ : Fin n),
      Y ⊆ X₁ ∧ w₀ ∈ Y ∧ (Y.ncard : ℝ) ≤ (X₁.ncard : ℝ) / 2 ∧
      (∀ w : Fin n, w ∈ X₁ ∧ w ∉ Y → ∃ q : G.Walk w w₀, q.IsPath ∧ q.length = 2 * d + 2 ∧
        (∀ z ∈ q.support, z = w ∨ z = w₀ ∨ z ∈ T₁.verts)) := by
  classical
  let D : Fin n → ℕ := fun z => T₁.spanningCoe.dist v₀ z
  have hpex : ∀ z, ∃ u, z ∈ T₁.verts → z ≠ v₀ → T₁.spanningCoe.Adj u z ∧ D u + 1 = D z := by
    intro z
    by_cases hz : z ∈ T₁.verts ∧ z ≠ v₀
    · obtain ⟨u, hu1, hu2⟩ := h42_pred (hT₁reach z hz.1) hz.2
      exact ⟨u, fun _ _ => ⟨hu1, hu2⟩⟩
    · exact ⟨z, fun a b => absurd ⟨a, b⟩ hz⟩
  choose par hpar using hpex
  have hit : ∀ s z, z ∈ T₁.verts → s ≤ D z → par^[s] z ∈ T₁.verts ∧ D (par^[s] z) + s = D z := by
    intro s
    induction s with
    | zero => intro z hz _; exact ⟨hz, by simp⟩
    | succ s ih =>
      intro z hz hs
      obtain ⟨h1, h2⟩ := ih z hz (by omega)
      have hne : par^[s] z ≠ v₀ := by
        intro he; rw [he] at h2; have : D v₀ = 0 := by simp [D]
        omega
      obtain ⟨h3, h4⟩ := hpar _ h1 hne
      rw [Function.iterate_succ_apply']
      exact ⟨T₁.edge_vert h3, by omega⟩
  have hstep : ∀ s z, z ∈ T₁.verts → s < D z → G.Adj (par^[s] z) (par^[s+1] z) := by
    intro s z hz hs
    obtain ⟨h1, h2⟩ := hit s z hz (by omega)
    have hne : par^[s] z ≠ v₀ := by
      intro he; rw [he] at h2; have : D v₀ = 0 := by simp [D]
      omega
    obtain ⟨h3, _⟩ := hpar _ h1 hne
    rw [Function.iterate_succ_apply']
    exact (T₁.adj_sub h3).symm
  have hD0 : ∀ z ∈ T₁.verts, D z = 0 → z = v₀ := fun z hz h0 =>
    (((hT₁reach z hz).dist_eq_zero_iff).mp h0).symm
  let L := j - 1
  let y' : Fin n → Fin n := fun x => if hx : x ∈ X₁ then y x hx else x
  have hy' : ∀ x ∈ X₁, y' x ∈ T₁.verts ∧ D (y' x) = L ∧ G.Adj x (y' x) := by
    intro x hx
    obtain ⟨h1, h2, h3⟩ := hy x hx
    simp only [y', dif_pos hx]
    refine ⟨h1, ?_, h3⟩
    simp only [CycleLengthsExp.WellSpread.level] at h2
    simp only [D, L]; omega
  let agree : ℕ → Prop := fun i => ∀ x ∈ X₁, ∀ x' ∈ X₁, par^[L - i] (y' x) = par^[L - i] (y' x')
  have hanc0 : ∀ x ∈ X₁, par^[L] (y' x) = v₀ := by
    intro x hx
    obtain ⟨h1, h2, _⟩ := hy' x hx
    obtain ⟨h3, h4⟩ := hit L (y' x) h1 (by omega)
    exact hD0 _ h3 (by omega)
  have hag0 : agree 0 := by
    intro x hx x' hx'; simp only [Nat.sub_zero]; rw [hanc0 x hx, hanc0 x' hx']
  let i := Nat.findGreatest agree L
  have hiL : i ≤ L := Nat.findGreatest_le L
  have hagi : agree i := Nat.findGreatest_spec (Nat.zero_le L) hag0
  let d := L - i
  let key : Fin n → Fin n := fun x => if i < L then par^[d - 1] (y' x) else x
  have hdist : ∃ a ∈ X₁, ∃ b ∈ X₁, key a ≠ key b := by
    by_cases hlt : i < L
    · by_contra hcon
      push Not at hcon
      have : agree (i + 1) := by
        intro x hx x' hx'
        have := hcon x hx x' hx'
        simp only [key, if_pos hlt] at this
        have e : L - (i + 1) = d - 1 := by omega
        rw [e]; exact this
      exact Nat.findGreatest_is_greatest (lt_add_one i) (by omega) this
    · obtain ⟨a, b, ha, hb, hab⟩ := (Set.one_lt_ncard_iff (Set.toFinite X₁)).mp (by omega)
      exact ⟨a, ha, b, hb, by simp only [key, if_neg hlt]; exact hab⟩
  let F : Fin n → Set (Fin n) := fun x => {x' | x' ∈ X₁ ∧ key x' = key x}
  have hFsub : ∀ x, F x ⊆ X₁ := fun x z hz => hz.1
  have hdist' := hdist
  obtain ⟨a0, ha0, _⟩ := hdist'
  obtain ⟨w₀, hw₀mem, hw₀min⟩ := (Set.toFinite X₁).toFinset.exists_min_image (fun x => (F x).ncard)
    ⟨a0, (Set.Finite.mem_toFinset _).mpr ha0⟩
  rw [Set.Finite.mem_toFinset] at hw₀mem
  have hw₀min' : ∀ x ∈ X₁, (F w₀).ncard ≤ (F x).ncard := fun x hx =>
    hw₀min x ((Set.Finite.mem_toFinset _).mpr hx)
  refine ⟨d, F w₀, w₀, hFsub w₀, ⟨hw₀mem, rfl⟩, ?_, ?_⟩
  · obtain ⟨a, ha, b, hb, hab⟩ := hdist
    obtain ⟨c, hc, hcne⟩ : ∃ c ∈ X₁, key c ≠ key w₀ := by
      by_cases h : key a = key w₀
      · exact ⟨b, hb, fun h' => hab (h.trans h'.symm)⟩
      · exact ⟨a, ha, h⟩
    have hdisj : Disjoint (F w₀) (F c) := by
      rw [Set.disjoint_left]; intro z hz1 hz2; exact hcne (hz2.2.symm.trans hz1.2)
    have h1 := Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)
    have h2 := Set.ncard_le_ncard (Set.union_subset (hFsub w₀) (hFsub c)) (Set.toFinite X₁)
    have h3 := hw₀min' c hc
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 2)]
    have : (F w₀).ncard * 2 ≤ X₁.ncard := by omega
    exact_mod_cast this
  · rintro w ⟨hw, hwY⟩
    have hkey : key w ≠ key w₀ := fun h => hwY ⟨hw, h⟩
    have hww₀ : w ≠ w₀ := fun h => hkey (by rw [h])
    obtain ⟨hyw1, hyw2, hyw3⟩ := hy' w hw
    obtain ⟨hyv1, hyv2, hyv3⟩ := hy' w₀ hw₀mem
    have e : par^[d] (y' w) = par^[d] (y' w₀) := hagi w hw w₀ hw₀mem
    have hchain : ∀ s s', s ≤ d → s' ≤ d → par^[s] (y' w) = par^[s'] (y' w₀) → s = d ∧ s' = d := by
      intro s s' hs hs' hss
      have h1 := (hit s (y' w) hyw1 (by omega)).2
      have h2 := (hit s' (y' w₀) hyv1 (by omega)).2
      rw [hss] at h1
      have hss' : s = s' := by omega
      subst hss'
      by_contra hcon
      have hsd : s < d := by omega
      have hlt : i < L := by omega
      apply hkey
      simp only [key, if_pos hlt]
      have e2 : d - 1 = (d - 1 - s) + s := by omega
      rw [e2, Function.iterate_add_apply, Function.iterate_add_apply, hss]
    have hinj : ∀ z, z ∈ T₁.verts → ∀ s ≤ D z, ∀ s' ≤ D z, par^[s] z = par^[s'] z → s = s' := by
      intro z hz s hs s' hs' h
      have h1 := (hit s z hz hs).2
      have h2 := (hit s' z hz hs').2
      rw [h] at h1; omega
    obtain ⟨qa, hqa1, hqa2⟩ := h42b_up par (y' w) d (fun s hs => hstep s (y' w) hyw1 (by omega))
    obtain ⟨qb, hqb1, hqb2⟩ := h42b_up par (y' w₀) d (fun s hs => hstep s (y' w₀) hyv1 (by omega))
    let A := (List.range (d+1)).map (fun s => par^[s] (y' w))
    let B := (List.range d).map (fun s => par^[s] (y' w₀))
    have hBtail : qb.support.reverse.tail = B.reverse := by
      rw [hqb2, List.tail_reverse, List.range_succ, List.map_append]
      simp [B]
    let full : G.Walk w w₀ :=
      (SimpleGraph.Walk.cons hyw3 (qa.append (qb.reverse.copy e.symm rfl))).concat hyv3.symm
    have hsup : full.support = (w :: (A ++ B.reverse)) ++ [w₀] := by
      simp only [full, SimpleGraph.Walk.support_concat, SimpleGraph.Walk.support_cons,
        SimpleGraph.Walk.support_append, SimpleGraph.Walk.support_copy]
      rw [SimpleGraph.Walk.support_reverse, hBtail, hqa2]
    have memA : ∀ z ∈ A, ∃ s, s ≤ d ∧ par^[s] (y' w) = z := by
      intro z hz
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hz
      exact ⟨s, by rw [List.mem_range] at hs; omega, rfl⟩
    have memB : ∀ z ∈ B.reverse, ∃ s, s < d ∧ par^[s] (y' w₀) = z := by
      intro z hz
      rw [List.mem_reverse] at hz
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hz
      exact ⟨s, by rw [List.mem_range] at hs; omega, rfl⟩
    have hAT : ∀ z ∈ A, z ∈ T₁.verts := by
      intro z hz; obtain ⟨s, hs, rfl⟩ := memA z hz; exact (hit s _ hyw1 (by omega)).1
    have hBT : ∀ z ∈ B.reverse, z ∈ T₁.verts := by
      intro z hz; obtain ⟨s, hs, rfl⟩ := memB z hz; exact (hit s _ hyv1 (by omega)).1
    refine ⟨full, ?_, ?_, ?_⟩
    · rw [SimpleGraph.Walk.isPath_def, hsup]
      rw [List.nodup_append, List.nodup_cons, List.nodup_append]
      refine ⟨⟨?_, ⟨?_, ?_, ?_⟩⟩, List.nodup_singleton _, ?_⟩
      · intro hmem
        rw [List.mem_append] at hmem
        rcases hmem with h | h
        · exact hX₁T₁ w hw (hAT w h)
        · exact hX₁T₁ w hw (hBT w h)
      · apply List.Nodup.map_on
        · intro s hs s' hs' h
          rw [List.mem_range] at hs hs'
          exact hinj _ hyw1 s (by omega) s' (by omega) h
        · exact List.nodup_range
      · rw [List.nodup_reverse]
        apply List.Nodup.map_on
        · intro s hs s' hs' h
          rw [List.mem_range] at hs hs'
          exact hinj _ hyv1 s (by omega) s' (by omega) h
        · exact List.nodup_range
      · intro a ha b hb hab
        obtain ⟨s, hs, rfl⟩ := memA a ha
        obtain ⟨s', hs', rfl⟩ := memB b hb
        have := hchain s s' hs (by omega) hab
        omega
      · intro a ha b hb hab
        rw [List.mem_singleton] at hb
        rw [hb] at hab
        rcases List.mem_cons.mp ha with h | h
        · exact hww₀ (h.symm.trans hab)
        · rw [List.mem_append] at h
          rcases h with h | h
          · exact hX₁T₁ w₀ hw₀mem (hab ▸ hAT a h)
          · exact hX₁T₁ w₀ hw₀mem (hab ▸ hBT a h)
    · simp only [full, SimpleGraph.Walk.length_concat, SimpleGraph.Walk.length_cons,
        SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_copy,
        SimpleGraph.Walk.length_reverse, hqa1, hqb1]
      omega
    · intro z hz
      rw [hsup] at hz
      rw [List.mem_append, List.mem_cons, List.mem_append, List.mem_singleton] at hz
      rcases hz with (h | h | h) | h
      · exact Or.inl h
      · exact Or.inr (Or.inr (hAT z h))
      · exact Or.inr (Or.inr (hBT z h))
      · exact Or.inr (Or.inl h)

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

theorem solution (n : ℕ) (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1)
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
    h42_branching n G T₁ v₀ X₁ j yy hT₁acyc hT₁reach hv₀T₁ hX₁T₁ hyy hX₁card2
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


