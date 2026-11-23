-- Prove2me | solution 1 for ChenCapacityTerminals.Exact.full_group_incidences
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:22:09.476117+00:00
-- url     : https://prove2.me/submissions/7d9a0282-4240-4de6-a4b6-e9865c21bcfd

import Definitions.Def_ChenCapacityTerminals_Exact_Construction

set_option autoImplicit false

open ChenCapacityTerminals.Exact

private lemma fullGroups_card {d : ℕ} {xs : List ℕ} {g : Finset ℕ}
    (hd : 1 ≤ d) (hxs : xs.Nodup) (hg : g ∈ fullGroups d xs) : g.card = d := by
  obtain ⟨i, hi, rfl⟩ := by simpa [fullGroups] using hg
  have hid : i * d + d ≤ xs.length := by
    have h := (Nat.lt_div_iff_mul_lt (show 0 < d by omega)).1 hi
    omega
  have hsub : ((xs.drop (i * d)).take d).Sublist xs :=
    (List.take_sublist d (xs.drop (i * d))).trans (List.drop_sublist (i * d) xs)
  rw [List.toFinset_card_of_nodup (hsub.nodup hxs)]
  simp only [List.length_take, List.length_drop]
  omega

private lemma fullGroups_subset {G : Network} {d : ℕ} {xs : List ℕ} {g : Finset ℕ}
    (hg : g ∈ fullGroups d xs) (hxs : xs.toFinset ⊆ G.vertices) :
    g ⊆ G.vertices := by
  obtain ⟨i, hi, rfl⟩ := by simpa [fullGroups] using hg
  intro u hu
  apply hxs
  simp only [List.mem_toFinset] at hu ⊢
  exact List.mem_of_mem_drop (List.mem_of_mem_take hu)

private lemma fullGroups_sum_card {d : ℕ} {xs : List ℕ}
    (hd : 1 ≤ d) (hxs : xs.Nodup) :
    ((fullGroups d xs).map Finset.card).sum = d * (xs.length / d) := by
  have hmap : (fullGroups d xs).map Finset.card =
      (fullGroups d xs).map (fun _ => d) :=
    List.map_congr_left fun g hg => fullGroups_card hd hxs hg
  rw [hmap]
  change (List.map (Function.const (Finset ℕ) d) (fullGroups d xs)).sum = _
  rw [List.map_const, List.sum_replicate]
  simp only [nsmul_eq_mul, fullGroups, List.length_map, List.length_range]
  exact Nat.mul_comm _ _

private lemma flatMap_fullGroups_sum_le {ι : Type} (d : ℕ) (l : List ι)
    (tails : ι → List ℕ) (hd : 1 ≤ d)
    (hnodup : ∀ A ∈ l, (tails A).Nodup) :
    ((l.flatMap fun A => fullGroups d (tails A)).map Finset.card).sum ≤
      (l.map fun A => (tails A).length).sum := by
  induction l with
  | nil => simp
  | cons A l ih =>
      have hA : (tails A).Nodup := hnodup A (by simp)
      have hl : ∀ B ∈ l, (tails B).Nodup := by
        intro B hB
        exact hnodup B (by simp [hB])
      simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons]
      apply Nat.add_le_add
      · rw [fullGroups_sum_card hd hA]
        simpa [Nat.mul_comm] using Nat.div_mul_le_self (tails A).length d
      · exact ih hl

private lemma exists_arc_of_mem_tails {G : Network} {A : Finset ℕ}
    {xs : List ℕ} (hs : SortedTails G A xs) {u : ℕ}
    (hu : u ∈ xs.toFinset) :
    ∃ e ∈ G.arcs, e.tail = u ∧ e.head ∈ A := by
  have hu' : u ∈ positiveExternalTails G A := by
    rw [← hs.2.1]
    exact hu
  have hpos : 0 < weight G {u} A := (Finset.mem_filter.mp hu').2
  by_contra hn
  push_neg at hn
  have hzero : (G.arcs.map fun e =>
      if e.tail ∈ ({u} : Finset ℕ) ∧ e.head ∈ A then e.capacity else 0) =
      G.arcs.map (fun _ => 0) := by
    apply List.map_congr_left
    intro e he
    simp only [Finset.mem_singleton]
    split_ifs with hcond
    · exact (hn e he hcond.1 hcond.2).elim
    · rfl
  rw [weight, hzero] at hpos
  simp at hpos

private lemma tail_pairs_card_le_arcs (G : Network) (r d : ℕ) (L : ℚ)
    (c : Construction) (hpart : Partition G.vertices (c.partitions (c.rounds - 1)))
    (htail : ∀ A ∈ unchangedSources G r ((L : ℝ) / (4 * d))
      (c.partitions (c.rounds - 1)), SortedTails G A (c.tails A)) :
    let S := unchangedSources G r ((L : ℝ) / (4 * d))
      (c.partitions (c.rounds - 1))
    (S.toList.map fun A => (c.tails A).length).sum ≤ G.arcs.length := by
  classical
  dsimp only
  let S := unchangedSources G r ((L : ℝ) / (4 * d))
    (c.partitions (c.rounds - 1))
  let P := S.sigma fun A => (c.tails A).toFinset
  have hPcard : P.card = (S.toList.map fun A => (c.tails A).length).sum := by
    calc
      P.card = ∑ A ∈ S, ((c.tails A).toFinset).card := Finset.card_sigma _ _
      _ = ∑ A ∈ S, (c.tails A).length := by
        apply Finset.sum_congr rfl
        intro A hA
        exact List.toFinset_card_of_nodup (htail A hA).1
      _ = _ := by simp
  let arcFor : ↥P → Arc := fun p => Classical.choose (by
    have hp := Finset.mem_sigma.mp p.property
    exact exists_arc_of_mem_tails (htail p.1.1 hp.1) hp.2)
  have arcFor_spec (p : ↥P) :
      arcFor p ∈ G.arcs ∧ (arcFor p).tail = p.1.2 ∧ (arcFor p).head ∈ p.1.1 := by
    exact Classical.choose_spec (by
      have hp := Finset.mem_sigma.mp p.property
      exact exists_arc_of_mem_tails (htail p.1.1 hp.1) hp.2)
  let f : ↥P → ↥G.arcs.toFinset := fun p =>
    ⟨arcFor p, by simpa using (arcFor_spec p).1⟩
  have hf : Function.Injective f := by
    intro p q hpq
    have heq : arcFor p = arcFor q := congrArg Subtype.val hpq
    have hfirst : p.1.1 = q.1.1 := by
      by_contra hne
      have hpS := (Finset.mem_sigma.mp p.property).1
      have hqS := (Finset.mem_sigma.mp q.property).1
      have hpOld : p.1.1 ∈ c.partitions (c.rounds - 1) := Finset.filter_subset _ _ hpS
      have hqOld : q.1.1 ∈ c.partitions (c.rounds - 1) := Finset.filter_subset _ _ hqS
      have hdisj := hpart.2.2 p.1.1 hpOld q.1.1 hqOld hne
      have hpHead := (arcFor_spec p).2.2
      have hqHead : (arcFor p).head ∈ q.1.1 := by
        rw [heq]
        exact (arcFor_spec q).2.2
      exact (Finset.disjoint_left.mp hdisj hpHead) hqHead
    have hsecond : p.1.2 = q.1.2 := by
      have hpTail := (arcFor_spec p).2.1
      have hqTail := (arcFor_spec q).2.1
      exact hpTail.symm.trans ((congrArg Arc.tail heq).trans hqTail)
    apply Subtype.ext
    exact Sigma.ext hfirst (heq_of_eq hsecond)
  have hcard : P.card ≤ G.arcs.toFinset.card := by
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hf
  rw [← hPcard]
  exact hcard.trans (List.toFinset_card_le G.arcs)

theorem solution (G : Network) (r d : ℕ) (L : ℚ) (b : ℕ → ℕ) (t : ℕ)
    (c : Construction) (hprep : Prepared G r) (hd : 1 ≤ d)
    (hdn : d ≤ G.vertices.card) (hL : 0 < L)
    (hc : LegalConstruction G r d L b t c) :
    let groups := (unchangedSources G r ((L : ℝ) / (4 * d))
      (c.partitions (c.rounds - 1))).toList.flatMap fun A => fullGroups d (c.tails A)
    (∀ g ∈ groups, g ⊆ G.vertices ∧ g.card = d) ∧
      (groups.map Finset.card).sum ≤ G.arcs.length := by
  classical
  dsimp only
  rcases hc with ⟨hrounds, hp0, hpart, hmerge, hlarge, hnew, hrep,
    hjnodup, hjlegal, hjcomplete, htail, hgreedy, hrest⟩
  let S := unchangedSources G r ((L : ℝ) / (4 * d))
    (c.partitions (c.rounds - 1))
  have hgroup : ∀ g ∈ S.toList.flatMap (fun A => fullGroups d (c.tails A)),
      g ⊆ G.vertices ∧ g.card = d := by
    intro g hg
    obtain ⟨A, hA, hg⟩ := List.mem_flatMap.mp hg
    have hAS : A ∈ S := by simpa using hA
    have hs := htail A hAS
    have hsub : (c.tails A).toFinset ⊆ G.vertices := by
      rw [hs.2.1]
      intro u hu
      exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hu).1).1
    exact ⟨fullGroups_subset hg hsub, fullGroups_card hd hs.1 hg⟩
  refine ⟨hgroup, ?_⟩
  apply (flatMap_fullGroups_sum_le d S.toList (fun A => c.tails A) hd (by
    intro A hA
    exact (htail A (by simpa using hA)).1)).trans
  exact tail_pairs_card_le_arcs G r d L c (hpart (c.rounds - 1) (Nat.sub_le _ _)) htail
