-- Prove2me | solution 1 for CycleLengthsExp.ManyLengths.bcr_branching
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T23:48:55.196985+00:00
-- url     : https://prove2.me/submissions/2097ce58-7341-4362-a4d8-9737c2098f0e

import Mathlib
import Definitions.Def_CycleLengthsExp_ManyLengths_Setting

open CycleLengthsExp CycleLengthsExp.ManyLengths
/-- Branching + T-leg (Friedman–Krivelevich, p. 14, proof of Theorem 2).

Setup: `T₁` is an acyclic subtree of `G` rooted at `v₀`, `X₁` is a set of
vertices outside `T₁` (at least 2 of them), and every `x ∈ X₁` has a chosen
attachment `y x ∈ T₁.verts` at level exactly `j` adjacent to `x` in `G`.
(Think of `X₁` as leaves attached to level `j` of `T₁`; the attachments
come from `tree_extension_attach`.)

Conclusion: there are a common distance `d`, a smallest branch `Y ⊆ X₁`
with `|Y| ≤ |X₁| / 2`, and a base vertex `w₀ ∈ Y`, such that for every
`w ∈ X₁ ∖ Y` there is a path `q` in `G` from `w` to `w₀` of length exactly
`2 * d + 2` whose support lies in `{w, w₀} ∪ T₁.verts`.

Proof sketch: choose the attachments `y` via choice. Let `C` be the set of
vertices `z ∈ T₁.verts` lying on every `v₀ → y_x` path in `T₁` (`v₀ ∈ C`).
Take `r ∈ C` maximizing `dist_{T₁}(v₀, r)` (finite nonempty max). Then
`dist_{T₁}(r, y_x) = (j - 1) - dist_{T₁}(v₀, r) =: d` is the SAME for all `x`,
by level additivity. Partition `X₁` by branch: `branch(x)` is the first
step from `r` on the path `r → y_x`, or `x` itself if `y_x = r`. There are
at least 2 classes (else a deeper vertex would lie on every path,
contradicting maximality of `r`, or all `y_x = r` and the branches are the
distinct `x`'s). Let `Y` be a smallest class, `w₀ ∈ Y`. For `w ∈ X₁ ∖ Y`,
the `T₁`-path `y_w → y_{w₀}` has length `2 * d`: the concatenation
(reverse of `r → y_w`) ++ (`r → y_{w₀}`) is a path because the two subpaths
from `r` start with different first steps (different branches), hence meet
only at `r` (tree path uniqueness). Transfer the `T₁`-walk to a `G`-walk by
step induction, then prepend/append the two attachment edges to get the
`T`-leg `q` of length `1 + 2 * d + 1`, with support in `{w, w₀} ∪ T₁.verts`.

This is DEEP INPUT A of the decomposition of
`CycleLengthsExp.ManyLengths.branch_cycles_repaired` (parent, Open): the
assembly consumes `d`, `Y`, `w₀` and the `T`-legs to build one cycle per
`w ∈ X₃`, with `X₃` the larger side of `X₁ ∖ Y` along `P`. -/
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

theorem solution (n : ℕ) (G : SimpleGraph (Fin n))
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


