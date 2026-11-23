-- Prove2me | solution 1 for ChenCapacityTerminals.Exact.unchanged_source_capacity
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:55:03.103173+00:00
-- url     : https://prove2.me/submissions/43b2fa16-1cb1-436f-8a9a-a3d7aade1547

import Definitions.Def_ChenCapacityTerminals_Exact_Construction

set_option autoImplicit false

open ChenCapacityTerminals.Exact

private lemma weight_finset (G : Network) (S A : Finset ℕ) :
    weight G S A = ∑ u ∈ S, weight G {u} A := by
  classical
  unfold weight
  induction G.arcs with
  | nil => simp
  | cons e es ih =>
      simp only [List.map_cons, List.sum_cons, Finset.mem_singleton]
      rw [ih, Finset.sum_add_distrib]
      have he : (if e.tail ∈ S ∧ e.head ∈ A then e.capacity else 0) =
          ∑ u ∈ S, if e.tail = u ∧ e.head ∈ A then e.capacity else 0 := by
        by_cases htail : e.tail ∈ S
        · rw [Finset.sum_eq_single e.tail]
          · simp [htail]
          · intro u hu hne
            simp [Ne.symm hne]
          · simp [htail]
        · simp only [htail, false_and, ↓reduceIte]
          symm
          apply Finset.sum_eq_zero
          intro u hu
          have hne : e.tail ≠ u := by
            intro heq
            subst u
            exact htail hu
          simp [hne]
      simp only [Finset.mem_singleton]
      rw [he]

private lemma weight_nonneg {G : Network} (hG : G.Valid) (S A : Finset ℕ) :
    0 ≤ weight G S A := by
  unfold weight
  apply List.sum_nonneg
  intro x hx
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
  split_ifs
  · exact (hG e he).2.2
  · exact le_rfl

private lemma cut_eq_positiveExternalTails {G : Network} (hG : G.Valid)
    (A : Finset ℕ) :
    cut G A = ∑ u ∈ positiveExternalTails G A, weight G {u} A := by
  classical
  unfold cut
  rw [weight_finset]
  unfold positiveExternalTails
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro u hu
  split_ifs with hpos
  · rfl
  · have hnonneg := weight_nonneg hG {u} A
    have hzero : weight G {u} A = 0 := le_antisymm (le_of_not_gt hpos) hnonneg
    simp [hzero]

private lemma greedy_hits {V : Finset ℕ} {groups : List (Finset ℕ)} {D : List ℕ}
    (hD : Greedy V groups D) {g : Finset ℕ} (hg : g ∈ groups) :
    ∃ v ∈ D.toFinset, v ∈ g := by
  induction D generalizing groups with
  | nil => simp [Greedy] at hD; simp [hD] at hg
  | cons v rest ih =>
      rw [Greedy] at hD
      by_cases hv : v ∈ g
      · exact ⟨v, by simp, hv⟩
      · have hg' : g ∈ groups.filter fun g => v ∉ g := by simp [hg, hv]
        obtain ⟨u, hu, hug⟩ := ih hD.2.2.2 hg'
        refine ⟨u, ?_, hug⟩
        simp only [List.mem_toFinset] at hu ⊢
        exact List.mem_cons_of_mem v hu

private lemma list_sum_le_length_mul {xs : List ℕ} {w : ℕ → ℝ} {q : ℝ}
    (h : ∀ u ∈ xs, w u ≤ q) : (xs.map w).sum ≤ xs.length * q := by
  calc
    (xs.map w).sum ≤ (xs.map fun _ => q).sum := List.sum_le_sum h
    _ = xs.length * q := by simp [nsmul_eq_mul]

private lemma fullGroups_drop_subset {d : ℕ} {xs : List ℕ}
    (hd : 1 ≤ d) (hlen : d ≤ xs.length) {g : Finset ℕ}
    (hg : g ∈ fullGroups d (xs.drop d)) : g ∈ fullGroups d xs := by
  obtain ⟨i, hi, rfl⟩ := by simpa [fullGroups] using hg
  simp only [fullGroups, List.mem_map, List.mem_range]
  refine ⟨i + 1, ?_, ?_⟩
  · have hi' : i < (xs.length - d) / d := by simpa using hi
    have hdiv : (xs.length - d) / d + 1 = xs.length / d := by
      calc
        (xs.length - d) / d + 1 = ((xs.length - d) + d) / d :=
          (Nat.add_div_right _ (by omega)).symm
        _ = xs.length / d := by rw [Nat.sub_add_cancel hlen]
    omega
  · simpa [List.drop_drop, Nat.add_mul, Nat.add_comm]

private lemma sorted_fullGroups_charge (d : ℕ) (xs : List ℕ) (D : Finset ℕ)
    (w : ℕ → ℝ) (q : ℝ) (hd : 1 ≤ d) (hxs : xs.Nodup)
    (hsort : xs.Pairwise fun u v => w v ≤ w u)
    (hnonneg : ∀ u, 0 ≤ w u) (hq : 0 ≤ q)
    (hbound : ∀ u ∈ xs, w u ≤ q)
    (hhit : ∀ g ∈ fullGroups d xs, ∃ v ∈ D, v ∈ g) :
    (xs.map w).sum ≤ d * q + d * ∑ v ∈ D, w v := by
  classical
  by_cases hshort : xs.length < d
  · have hsum : 0 ≤ ∑ v ∈ D, w v := Finset.sum_nonneg fun u hu => hnonneg u
    calc
      (xs.map w).sum ≤ xs.length * q := list_sum_le_length_mul hbound
      _ ≤ d * q := by
        apply mul_le_mul_of_nonneg_right _ hq
        exact_mod_cast (Nat.le_of_lt hshort)
      _ ≤ d * q + d * ∑ v ∈ D, w v :=
        le_add_of_nonneg_right (mul_nonneg (by positivity) hsum)
  · have hlen : d ≤ xs.length := Nat.le_of_not_gt hshort
    let first := (xs.take d).toFinset
    have hg0 : first ∈ fullGroups d xs := by
      simp only [fullGroups, List.mem_map, List.mem_range]
      refine ⟨0, by simp [Nat.div_pos hlen (by omega)], by simp [first]⟩
    obtain ⟨v0, hv0D, hv0g0⟩ := hhit first hg0
    have hv0first : v0 ∈ xs.take d := by simpa [first] using hv0g0
    have happend : xs.take d ++ xs.drop d = xs := List.take_append_drop d xs
    have hxappend : (xs.take d ++ xs.drop d).Nodup := by rwa [happend]
    have hsortappend : (xs.take d ++ xs.drop d).Pairwise (fun u v => w v ≤ w u) := by
      rwa [happend]
    have hnodup := List.nodup_append.mp hxappend
    have hsorts := List.pairwise_append.mp hsortappend
    have hrestbound : ∀ u ∈ xs.drop d, w u ≤ w v0 := by
      intro u hu
      exact hsorts.2.2 v0 hv0first u hu
    have hresthit : ∀ g ∈ fullGroups d (xs.drop d), ∃ v ∈ D \ first, v ∈ g := by
      intro g hg
      obtain ⟨v, hvD, hvg⟩ := hhit g (fullGroups_drop_subset hd hlen hg)
      have hvrest : v ∈ xs.drop d := by
        obtain ⟨i, hi, rfl⟩ := by simpa [fullGroups] using hg
        have hv' : v ∈ ((xs.drop d).drop (i * d)).take d := by
          simpa using hvg
        exact List.mem_of_mem_drop (List.mem_of_mem_take hv')
      refine ⟨v, Finset.mem_sdiff.mpr ⟨hvD, ?_⟩, hvg⟩
      intro hvfirst
      have hvtake : v ∈ xs.take d := by simpa [first] using hvfirst
      exact hnodup.2.2 v hvtake v hvrest rfl
    have hrec := sorted_fullGroups_charge d (xs.drop d) (D \ first) w (w v0) hd
      hnodup.2.1 hsorts.2.1 hnonneg (hnonneg v0) hrestbound hresthit
    have hfirst : ((xs.take d).map w).sum ≤ d * q := by
      calc
        ((xs.take d).map w).sum ≤ (xs.take d).length * q :=
          list_sum_le_length_mul (fun u hu => hbound u (List.mem_of_mem_take hu))
        _ = d * q := by simp [List.length_take, Nat.min_eq_left hlen]
    have hv0not : v0 ∉ D \ first := by simp [hv0g0]
    have hinsert : insert v0 (D \ first) ⊆ D := by
      intro u hu
      simp only [Finset.mem_insert, Finset.mem_sdiff] at hu
      rcases hu with rfl | hu
      · exact hv0D
      · exact hu.1
    have hset : w v0 + (∑ v ∈ D \ first, w v) ≤ ∑ v ∈ D, w v := by
      calc
        w v0 + (∑ v ∈ D \ first, w v) = ∑ v ∈ insert v0 (D \ first), w v :=
          (Finset.sum_insert hv0not).symm
        _ ≤ ∑ v ∈ D, w v := Finset.sum_le_sum_of_subset_of_nonneg hinsert
          (fun u hu hnot => hnonneg u)
    have hsetmul := mul_le_mul_of_nonneg_left hset (show 0 ≤ (d : ℝ) by positivity)
    calc
      (xs.map w).sum = ((xs.take d).map w).sum + ((xs.drop d).map w).sum := by
        conv_lhs => rw [← happend]
        simp
      _ ≤ d * q + (d * w v0 + d * ∑ v ∈ D \ first, w v) := add_le_add hfirst hrec
      _ ≤ d * q + d * ∑ v ∈ D, w v := by nlinarith
termination_by xs.length
decreasing_by
  simp_wf
  omega

theorem solution (G : Network) (r d : ℕ) (L : ℚ) (b : ℕ → ℕ) (t : ℕ)
    (c : Construction) (hprep : Prepared G r) (hd : 1 ≤ d)
    (hdn : d ≤ G.vertices.card) (hL : 0 < L)
    (hc : LegalConstruction G r d L b t c) :
    RootLowerBound G r L → ∀ A ∈ unchangedSources G r ((L : ℝ) / (4 * d))
      (c.partitions (c.rounds - 1)),
    3 * (L : ℝ) / (4 * d) ≤ weight G (c.greedy.toFinset \ A) A := by
  classical
  intro hroot A hA
  have hA0 := hA
  simp only [unchangedSources, Finset.mem_filter] at hA
  rcases hc with ⟨hrounds, hinit, hparts, hmerge, hnew, hfinal, hreps,
    hjoinnodup, hjoinlegal, hjoincomplete, hsorted, hgreedy, hfinalnodup,
    hfinalset, hfinallegal, hretained⟩
  have hG : G.Valid := hprep.1
  let w : ℕ → ℝ := fun u => weight G {u} A
  let tails := c.tails A
  let D := c.greedy.toFinset
  let charged := D \ A
  have hnonneg : ∀ u, 0 ≤ w u := fun u => weight_nonneg hG {u} A
  have hsortA := hsorted A hA0
  have htailpos : ∀ u ∈ tails, u ∈ positiveExternalTails G A := by
    intro u hu
    rw [← hsortA.2.1]
    exact List.mem_toFinset.mpr hu
  have htailbound : ∀ u ∈ tails, w u ≤ (L : ℝ) / (4 * d) := by
    intro u hu
    have hpos := htailpos u hu
    have huV : u ∈ G.vertices := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hpos).1).1
    have huA : u ∉ A := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hpos).1).2
    have huUnion : u ∈ Finset.biUnion (c.partitions (c.rounds - 1)) id := by
      rw [(hparts (c.rounds - 1) (Nat.sub_le _ _)).2.1]
      exact huV
    obtain ⟨P, hP, huP⟩ := Finset.mem_biUnion.mp huUnion
    have hPne : P ≠ A := by
      intro heq
      subst P
      exact huA huP
    apply le_of_not_gt
    intro hheavy
    have hPA : P ⊆ A := hA.2.2.2 P hP A hA.1 subset_rfl
      ⟨hPne, u, huP, hheavy⟩
    exact huA (hPA huP)
  have hhit : ∀ g ∈ fullGroups d tails, ∃ v ∈ charged, v ∈ g := by
    intro g hg
    obtain ⟨v, hvD, hvg⟩ := greedy_hits hgreedy (by
      simp only [List.mem_flatMap]
      exact ⟨A, Finset.mem_toList.mpr hA0, hg⟩)
    have hvlist : v ∈ tails := by
      obtain ⟨i, hi, rfl⟩ := by simpa [fullGroups] using hg
      have hv' : v ∈ (tails.drop (i * d)).take d := by simpa using hvg
      exact List.mem_of_mem_drop (List.mem_of_mem_take hv')
    have hvA : v ∉ A := by
      have hvpos := htailpos v hvlist
      exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hvpos).1).2
    exact ⟨v, Finset.mem_sdiff.mpr ⟨hvD, hvA⟩, hvg⟩
  have hq : 0 ≤ (L : ℝ) / (4 * d) := by positivity
  have hcharge := sorted_fullGroups_charge d tails charged w
    ((L : ℝ) / (4 * d)) hd hsortA.1 hsortA.2.2 hnonneg hq htailbound hhit
  have hcutlist : cut G A = (tails.map w).sum := by
    rw [cut_eq_positiveExternalTails hG]
    calc
      ∑ u ∈ positiveExternalTails G A, w u = ∑ u ∈ tails.toFinset, w u := by
        rw [hsortA.2.1]
      _ = (tails.map w).sum := List.sum_toFinset w hsortA.1
  have hcutcharge : cut G A ≤ d * ((L : ℝ) / (4 * d)) +
      d * ∑ v ∈ charged, w v := by
    rw [hcutlist]
    exact hcharge
  have hAp : A ∈ c.partitions (c.rounds - 1) := hA.1
  have hApart : A.Nonempty ∧ A ⊆ G.vertices :=
    (hparts (c.rounds - 1) (Nat.sub_le _ _)).1 A hAp
  have hLA : (L : ℝ) ≤ cut G A := hroot A ⟨hApart.2, hApart.1, hA.2.1⟩
  have hsumtarget : weight G charged A = ∑ v ∈ charged, w v := weight_finset _ _ _
  have hmain : (L : ℝ) ≤ d * ((L : ℝ) / (4 * d)) + d * weight G charged A := by
    rw [hsumtarget]
    exact hLA.trans hcutcharge
  change 3 * (L : ℝ) / (4 * d) ≤ weight G charged A
  apply (div_le_iff₀ (show 0 < (4 : ℝ) * d by positivity)).2
  have hid : (d : ℝ) * ((L : ℝ) / (4 * d)) = (L : ℝ) / 4 := by
    field_simp
    <;> ring
  nlinarith
