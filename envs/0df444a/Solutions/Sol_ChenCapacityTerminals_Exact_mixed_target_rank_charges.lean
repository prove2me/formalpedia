-- Prove2me | solution 1 for ChenCapacityTerminals.Exact.mixed_target_rank_charges
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T07:44:19.986327+00:00
-- url     : https://prove2.me/submissions/5b492a38-aae5-4fe9-b349-95df86f131dc

import Definitions.Def_ChenCapacityTerminals_Exact_GuideTargets

set_option autoImplicit false

open ChenCapacityTerminals.Exact

private structure GuideFacts (G : Network) (r d : ℕ) (L : ℚ) (b : ℕ → ℕ) (t : ℕ)
    (c : Construction) : Prop where
  rounds : 1 ≤ c.rounds
  initial : c.partitions 0 = G.vertices.image (fun v => {v})
  parts : ∀ i ≤ c.rounds, Partition G.vertices (c.partitions i)
  merge : ∀ i < c.rounds, c.partitions (i + 1) = mergeRound G ((L : ℝ) / (4 * d)) (c.partitions i)
  rep : ∀ i ≤ c.rounds, ∀ C ∈ c.partitions i, c.representative C ∈ C
  joinsNodup : (c.joins.map JoinGuide.parent).Nodup
  joins : ∀ j ∈ c.joins, LegalJoin G ((L : ℝ) / (4 * d)) c.representative j ∧
    ∃ i < c.rounds, j.parent ∈ c.partitions (i + 1) ∧ j.parent ∉ c.partitions i ∧
      j.children = (c.partitions i).filter (fun C => C ⊆ j.parent)
  complete : ∀ i < c.rounds, ∀ C ∈ c.partitions (i + 1), C ∉ c.partitions i →
    ∃ j ∈ c.joins, j.parent = C
  finalNodup : (c.finalEdges.map Prod.snd).Nodup
  finalSet : (c.finalEdges.map Prod.snd).toFinset =
    c.partitions c.rounds \ c.finalSources G ((L : ℝ) / (4 * d))

private lemma guideFacts {G : Network} {r d : ℕ} {L : ℚ} {b : ℕ → ℕ} {t : ℕ}
    {c : Construction} (hc : LegalConstruction G r d L b t c) : GuideFacts G r d L b t c := by
  rcases hc with ⟨hR, hp0, hpart, hmerge, hfail, hstop, hrep, hjnN, hjoins, hcomp,
    htails, hgreedy, hfnN, hfnset, hfinwit, hret⟩
  exact ⟨hR, hp0, hpart, hmerge, hrep, hjnN, hjoins, hcomp, hfnN, hfnset⟩

private lemma part_nonempty {V : Finset ℕ} {P : Parts} {A : Finset ℕ}
    (h : Partition V P) (hA : A ∈ P) : A.Nonempty := (h.1 A hA).1

private lemma part_subset {V : Finset ℕ} {P : Parts} {A : Finset ℕ}
    (h : Partition V P) (hA : A ∈ P) : A ⊆ V := (h.1 A hA).2

private lemma part_eq_of_intersects {V : Finset ℕ} {P : Parts} {A B : Finset ℕ}
    (h : Partition V P) (hA : A ∈ P) (hB : B ∈ P)
    (hx : (A ∩ B).Nonempty) : A = B := by
  by_contra hne
  obtain ⟨x, hx⟩ := hx
  rw [Finset.mem_inter] at hx
  exact (Finset.disjoint_left.mp (h.2.2 A hA B hB hne)) hx.1 hx.2

private lemma child_subset_parent {j : JoinGuide} {A : Finset ℕ}
    (hj : Partition j.parent j.children) (hA : A ∈ j.children) : A ⊆ j.parent := by
  intro x hx
  have hx' : x ∈ j.children.biUnion id := by
    simp only [Finset.mem_biUnion]
    exact ⟨A, hA, hx⟩
  rw [hj.2.1] at hx'
  exact hx'

private lemma child_card_lt {j : JoinGuide} {A : Finset ℕ}
    (h2 : 2 ≤ j.children.card) (hj : Partition j.parent j.children)
    (hA : A ∈ j.children) : A.card < j.parent.card := by
  have hproper : A ⊂ j.parent := by
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨child_subset_parent hj hA, ?_⟩
    intro hAp
    obtain ⟨B, C, hB, hC, hBC⟩ := Finset.one_lt_card_iff.mp (by omega : 1 < j.children.card)
    by_cases hBA : B = A
    · subst B
      have hCne : C ≠ A := fun h => hBC h.symm
      have hd := hj.2.2 A hA C hC hCne.symm
      obtain ⟨x, hx⟩ := part_nonempty hj hC
      have hxA : x ∈ A := by rw [hAp]; exact child_subset_parent hj hC hx
      exact (Finset.disjoint_left.mp hd) hxA hx
    · have hAne : A ≠ B := fun h => hBA h.symm
      have hd := hj.2.2 A hA B hB hAne
      obtain ⟨x, hx⟩ := part_nonempty hj hB
      have hxA : x ∈ A := by rw [hAp]; exact child_subset_parent hj hB hx
      exact (Finset.disjoint_left.mp hd) hxA hx
  exact Finset.card_lt_card hproper

private lemma merge_coarsens {G : Network} {τ : ℝ} {P : Parts} {A : Finset ℕ}
    (hA : A ∈ P) : ∃ D ∈ mergeRound G τ P, A ⊆ D := by
  classical
  have hscc : A ∈ sccParts G τ P A := Finset.mem_filter.mpr
    ⟨hA, Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
  refine ⟨(sccParts G τ P A).biUnion id, Finset.mem_image.mpr ⟨A, hA, rfl⟩, ?_⟩
  intro x hx
  simp only [Finset.mem_biUnion]
  exact ⟨A, hscc, hx⟩

private lemma part_later {G : Network} {r d : ℕ} {L : ℚ} {b : ℕ → ℕ} {t : ℕ}
    {c : Construction} (F : GuideFacts G r d L b t c)
    {i k : ℕ} (hik : i ≤ k) (hk : k ≤ c.rounds) {A : Finset ℕ}
    (hA : A ∈ c.partitions i) : ∃ D ∈ c.partitions k, A ⊆ D := by
  induction k generalizing i A with
  | zero =>
      have hi : i = 0 := by omega
      subst i
      exact ⟨A, hA, fun _ hx => hx⟩
  | succ k ih =>
      by_cases hik' : i = k + 1
      · subst i
        exact ⟨A, hA, fun _ hx => hx⟩
      · have hik0 : i ≤ k := by omega
        obtain ⟨D, hD, hAD⟩ := ih hik0 (by omega) hA
        rw [F.merge k (show k < c.rounds by omega)]
        obtain ⟨E, hE, hDE⟩ := merge_coarsens hD
        exact ⟨E, hE, hAD.trans hDE⟩

private lemma part_laminar {G : Network} {r d : ℕ} {L : ℚ} {b : ℕ → ℕ} {t : ℕ}
    {c : Construction} (F : GuideFacts G r d L b t c)
    {i k : ℕ} (hik : i ≤ k) (hk : k ≤ c.rounds) {A B : Finset ℕ}
    (hA : A ∈ c.partitions i) (hB : B ∈ c.partitions k)
    (hx : (A ∩ B).Nonempty) : A ⊆ B := by
  obtain ⟨D, hD, hAD⟩ := part_later F hik hk hA
  have hDB : D = B := part_eq_of_intersects (F.parts k hk) hD hB (by
    obtain ⟨x, hx⟩ := hx
    rw [Finset.mem_inter] at hx
    exact ⟨x, Finset.mem_inter.mpr ⟨hAD hx.1, hx.2⟩⟩)
  rwa [← hDB]

private lemma nonsingleton_has_join {G : Network} {r d : ℕ} {L : ℚ} {b : ℕ → ℕ} {t : ℕ}
    {c : Construction} (F : GuideFacts G r d L b t c)
    {k : ℕ} (hk : k ≤ c.rounds) {C : Finset ℕ} (hC : C ∈ c.partitions k) :
    C.card = 1 ∨ ∃ j ∈ c.joins, j.parent = C := by
  induction k with
  | zero =>
      left
      rw [F.initial] at hC
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hC
      simp
  | succ k ih =>
      by_cases hold : C ∈ c.partitions k
      · exact ih (by omega) hold
      · right
        exact F.complete k (by omega) C hC hold

private lemma join_scc {G : Network} {r d : ℕ} {L : ℚ} {b : ℕ → ℕ} {t : ℕ}
    {c : Construction} (F : GuideFacts G r d L b t c) {j : JoinGuide} (hj : j ∈ c.joins) :
    ∃ i < c.rounds, ∃ D ∈ c.partitions i,
      j.children = sccParts G ((L : ℝ) / (4 * d)) (c.partitions i) D := by
  classical
  obtain ⟨hlegal, i, hi, hparent, hnew, hchildren⟩ := F.joins j hj
  rw [F.merge i hi] at hparent
  simp only [mergeRound, Finset.mem_image] at hparent
  obtain ⟨D, hD, hparentD⟩ := hparent
  refine ⟨i, hi, D, hD, ?_⟩
  ext A
  constructor
  · intro hA
    have hAold : A ∈ c.partitions i := by rw [hchildren] at hA; exact (Finset.mem_filter.mp hA).1
    have hAsub : A ⊆ j.parent := by rw [hchildren] at hA; exact (Finset.mem_filter.mp hA).2
    obtain ⟨x, hx⟩ := part_nonempty (F.parts i (by omega)) hAold
    have hxparent : x ∈ j.parent := hAsub hx
    rw [← hparentD] at hxparent
    obtain ⟨E, hE, hxE⟩ := Finset.mem_biUnion.mp hxparent
    have hEold : E ∈ c.partitions i := (Finset.mem_filter.mp hE).1
    have hAE : A = E := part_eq_of_intersects (F.parts i (by omega)) hAold hEold
      ⟨x, Finset.mem_inter.mpr ⟨hx, hxE⟩⟩
    rwa [hAE]
  · intro hA
    have hAfilter := Finset.mem_filter.mp hA
    have hAold : A ∈ c.partitions i := hAfilter.1
    have hAsub : A ⊆ j.parent := by
      intro x hx
      rw [← hparentD]
      exact Finset.mem_biUnion.mpr ⟨A, hA, hx⟩
    rw [hchildren]
    exact Finset.mem_filter.mpr ⟨hAold, hAsub⟩

private lemma join_reach {G : Network} {τ : ℝ} {c : Construction} {j : JoinGuide} {i : ℕ} {D : Finset ℕ}
    (hscc : j.children = sccParts G τ (c.partitions i) D)
    {A B : Finset ℕ} (hA : A ∈ j.children) (hB : B ∈ j.children) :
    quotientReach G τ (c.partitions i) A B := by
  classical
  have hAs0 : A ∈ sccParts G τ (c.partitions i) D := by rwa [← hscc]
  have hBs0 : B ∈ sccParts G τ (c.partitions i) D := by rwa [← hscc]
  exact (Finset.mem_filter.mp hAs0).2.2.trans (Finset.mem_filter.mp hBs0).2.1

private lemma scc_restricted_reach {G : Network} {τ : ℝ} {P S : Parts} {a b : Finset ℕ}
    (ha : a ∈ S) (hb : b ∈ S) (hpath : quotientReach G τ P a b) (hrev : quotientReach G τ P b a)
    (hclosed : ∀ z, z ∈ P → quotientReach G τ P a z → quotientReach G τ P z a → z ∈ S) :
    Relation.ReflTransGen (fun A C => A ∈ S ∧ C ∈ S ∧ quotientEdge G τ A C) a b := by
  induction hpath using Relation.ReflTransGen.head_induction_on with
  | refl => exact Relation.ReflTransGen.refl
  | @head a z haz hzb ih =>
      have haz' : quotientReach G τ P a z := Relation.ReflTransGen.single haz
      have hza : quotientReach G τ P z a := hzb.trans hrev
      have hz : z ∈ S := hclosed z haz.2.1 haz' hza
      have hbz : quotientReach G τ P b z := hrev.trans haz'
      have hclosedz : ∀ y, y ∈ P → quotientReach G τ P z y → quotientReach G τ P y z → y ∈ S := by
        intro y hyP hzy hyz
        apply hclosed y hyP (haz'.trans hzy)
        exact hyz.trans hza
      exact Relation.ReflTransGen.head ⟨ha, hz, haz.2.2⟩ (ih hz hbz hclosedz)

private lemma reach_cross {α : Type*} {q : α → α → Prop} {S : Finset α} {a b : α}
    (h : Relation.ReflTransGen q a b) (ha : a ∈ S) (hb : b ∉ S) :
    ∃ u v, q u v ∧ u ∈ S ∧ v ∉ S := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact False.elim (hb ha)
  | @head a z haz hzb ih =>
      by_cases hz : z ∈ S
      · exact ih hz
      · exact ⟨a, z, haz, ha, hz⟩

private lemma weight_mono_right {G : Network} (hG : G.Valid) {u : ℕ} {A B : Finset ℕ}
    (hAB : A ⊆ B) : weight G {u} A ≤ weight G {u} B := by
  unfold weight
  apply List.sum_le_sum
  intro e he
  by_cases hu : e.tail = u
  · by_cases hA : e.head ∈ A
    · have hB : e.head ∈ B := hAB hA
      simp [hu, hA, hB]
    · by_cases hB : e.head ∈ B
      · simp [hu, hA, hB]
        exact (hG e he).2.2
      · simp [hu, hA, hB]
  · simp [hu]

private lemma mixed_part_charge_aux {G : Network} {r d : ℕ} {L : ℚ} {b : ℕ → ℕ} {t : ℕ}
    {c : Construction} (F : GuideFacts G r d L b t c) (hG : G.Valid) (X : Finset ℕ) :
    ∀ n C k, C.card = n → k ≤ c.rounds → C ∈ c.partitions k →
      (C ∩ X).Nonempty → ¬ C ⊆ X →
      ∃ u, u ∈ C ∧ u ∉ X ∧ ((L : ℝ) / (4 * d)) < weight G {u} (C ∩ X) := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro C k hcard hk hC hin hout
      rcases nonsingleton_has_join F hk hC with hsing | ⟨j, hj, hjp⟩
      · obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hsing
        obtain ⟨x, hx⟩ := hin
        rw [Finset.mem_inter] at hx
        obtain ⟨y, hyC, hyX⟩ := Finset.not_subset.mp hout
        simp only [Finset.mem_singleton] at hx hyC
        have hxv : x = v := hx.1
        subst x
        subst y
        exact False.elim (hyX hx.2)
      · obtain ⟨hlegal, i, hi, hparent, hnew, hchildren⟩ := F.joins j hj
        rcases hlegal with ⟨h2, hpartj, hheavy, hmax, hrep, hedgeN, hedgeSet, hedgeW, hreach⟩
        have hCsub : ∀ A ∈ j.children, A ⊆ C := by
          intro A hA
          rw [← hjp]
          exact child_subset_parent hpartj hA
        by_cases hchild : ∃ A ∈ j.children, (A ∩ X).Nonempty ∧ ¬ A ⊆ X
        · obtain ⟨A, hA, hAin, hAout⟩ := hchild
          have hAi : A ∈ c.partitions i := by rw [hchildren] at hA; exact (Finset.mem_filter.mp hA).1
          have hlt : A.card < n := by rw [← hcard, ← hjp]; exact child_card_lt h2 hpartj hA
          obtain ⟨u, huA, huX, hcharge⟩ := ih A.card hlt A i rfl (by omega) hAi hAin hAout
          refine ⟨u, hCsub A hA huA, huX, lt_of_lt_of_le hcharge ?_⟩
          exact weight_mono_right hG (by
            intro x hx
            rw [Finset.mem_inter] at hx ⊢
            exact ⟨hCsub A hA hx.1, hx.2⟩)
        · push_neg at hchild
          obtain ⟨i', hi', D, hDi, hscc⟩ := join_scc F hj
          have hmono : ∀ A ∈ j.children, A ⊆ X ∨ ∀ x ∈ A, x ∉ X := by
            intro A hA
            by_cases hAX : A ⊆ X
            · exact Or.inl hAX
            · right
              have hEmpty : ¬ (A ∩ X).Nonempty := by intro hn; exact hAX (hchild A hA hn)
              intro x hxA hxX
              exact hEmpty ⟨x, Finset.mem_inter.mpr ⟨hxA, hxX⟩⟩
          obtain ⟨x, hx⟩ := hin
          rw [Finset.mem_inter] at hx
          have hxUnion : x ∈ j.parent := by rw [hjp]; exact hx.1
          rw [← hpartj.2.1] at hxUnion
          obtain ⟨A, hA, hxA⟩ := Finset.mem_biUnion.mp hxUnion
          have hAX : A ⊆ X := (hmono A hA).resolve_right (fun h => h x hxA hx.2)
          obtain ⟨y, hyC, hyX⟩ := Finset.not_subset.mp hout
          have hyUnion : y ∈ j.parent := by rw [hjp]; exact hyC
          rw [← hpartj.2.1] at hyUnion
          obtain ⟨B, hB, hyB⟩ := Finset.mem_biUnion.mp hyUnion
          have hBnX : ¬ B ⊆ X := by intro h; exact hyX (h hyB)
          have hpath := join_reach hscc hB hA
          have hrev := join_reach hscc hA hB
          have hBscc : B ∈ sccParts G ((L : ℝ) / (4 * d)) (c.partitions i') D := by rwa [← hscc]
          have hBD := (Finset.mem_filter.mp hBscc).2
          have hclosed : ∀ z, z ∈ c.partitions i' →
              quotientReach G ((L : ℝ) / (4 * d)) (c.partitions i') B z →
              quotientReach G ((L : ℝ) / (4 * d)) (c.partitions i') z B → z ∈ j.children := by
            intro z hz hBz hzB
            rw [hscc]
            exact Finset.mem_filter.mpr ⟨hz, hBD.1.trans hBz, hzB.trans hBD.2⟩
          have hrestricted : Relation.ReflTransGen
              (fun U V => U ∈ j.children ∧ V ∈ j.children ∧ quotientEdge G ((L : ℝ) / (4 * d)) U V) B A :=
            scc_restricted_reach hB hA hpath hrev hclosed
          let S : Parts := j.children.filter (fun Z => ¬ Z ⊆ X)
          have hBS : B ∈ S := by simp [S, hB, hBnX]
          have hAS : A ∉ S := by simp [S, hA, hAX]
          obtain ⟨U, V, hUV, hUS, hVS⟩ := reach_cross hrestricted hBS hAS
          have hU : U ∈ j.children := hUV.1
          have hV : V ∈ j.children := hUV.2.1
          have hUx : ∀ z ∈ U, z ∉ X := by
            have hUn : ¬ U ⊆ X := by simpa [S] using (Finset.mem_filter.mp hUS).2
            exact (hmono U hU).resolve_left hUn
          have hVX : V ⊆ X := by
            have hnot : V ∉ S := hVS
            simp only [S, Finset.mem_filter, not_and, not_not] at hnot
            exact hnot hV
          obtain ⟨hUne, u, huU, hcharge⟩ := hUV.2.2
          refine ⟨u, hCsub U hU huU, hUx u huU, lt_of_lt_of_le hcharge ?_⟩
          apply weight_mono_right hG
          intro z hz
          exact Finset.mem_inter.mpr ⟨hCsub V hV hz, hVX hz⟩

private lemma target_origin {G : Network} {r d : ℕ} {L : ℚ} {b : ℕ → ℕ} {t : ℕ}
    {c : Construction} (F : GuideFacts G r d L b t c) {e : TargetedGuideEdge}
    (he : e ∈ c.targetedGuide G ((L : ℝ) / (4 * d))) :
    (∃ j, j ∈ c.joins ∧ ∃ i < c.rounds, ∃ u, (u, e.target) ∈ j.edges ∧
      e.target ∈ c.partitions i ∧ e.target ∈ j.children ∧
      j.parent ∈ c.partitions (i + 1)) ∨ e.target ∈ c.partitions c.rounds := by
  classical
  simp only [Construction.targetedGuide, List.mem_append, List.mem_flatMap, List.mem_map,
    Finset.mem_toList] at he
  rcases he with (⟨j, hj, ⟨u, C⟩, hp, heq⟩ | ⟨p, hp, heq⟩) | ⟨C, hC, heq⟩
  · left
    cases heq
    obtain ⟨hlegal, i, hi, hparent, hnew, hchildren⟩ := F.joins j hj
    have hCset : C ∈ (j.edges.map Prod.snd).toFinset :=
      List.mem_toFinset.mpr (List.mem_map.mpr ⟨(u, C), hp, rfl⟩)
    rw [hlegal.2.2.2.2.2.2.1] at hCset
    have hCchild : C ∈ j.children := (Finset.mem_sdiff.mp hCset).1
    have hCi : C ∈ c.partitions i := by rw [hchildren] at hCchild; exact (Finset.mem_filter.mp hCchild).1
    exact ⟨j, hj, i, hi, u, hp, hCi, (Finset.mem_sdiff.mp hCset).1, hparent⟩
  · right
    cases heq
    have hCset : p.2 ∈ (c.finalEdges.map Prod.snd).toFinset :=
      List.mem_toFinset.mpr (List.mem_map.mpr ⟨p, hp, rfl⟩)
    rw [F.finalSet] at hCset
    exact (Finset.mem_sdiff.mp hCset).1
  · right
    cases heq
    exact (Finset.mem_filter.mp hC).1

private lemma target_head_eq {G : Network} {τ : ℝ} {c : Construction} {e : TargetedGuideEdge}
    (he : e ∈ c.targetedGuide G τ) : e.head = c.representative e.target := by
  classical
  simp only [Construction.targetedGuide, List.mem_append, List.mem_flatMap, List.mem_map,
    Finset.mem_toList] at he
  rcases he with (⟨j, hj, p, hp, heq⟩ | ⟨p, hp, heq⟩) | ⟨C, hC, heq⟩
  · cases heq
    rfl
  · cases heq
    rfl
  · cases heq
    rfl

private lemma target_head {G : Network} {r d : ℕ} {L : ℚ} {b : ℕ → ℕ} {t : ℕ}
    {c : Construction} (F : GuideFacts G r d L b t c) {e : TargetedGuideEdge}
    (he : e ∈ c.targetedGuide G ((L : ℝ) / (4 * d))) : e.head ∈ e.target := by
  rw [target_head_eq he]
  rcases target_origin F he with ⟨j, hj, i, hi, u, hp, hAi, hAc, hP⟩ | hAi
  · exact F.rep i (by omega) e.target hAi
  · exact F.rep c.rounds le_rfl e.target hAi

private lemma not_straddling_singleton {A X : Finset ℕ}
    (hin : (A ∩ X).Nonempty) (hout : ¬ A ⊆ X) : A.card ≠ 1 := by
  intro hsing
  obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hsing
  obtain ⟨x, hx⟩ := hin
  rw [Finset.mem_inter] at hx
  obtain ⟨y, hyC, hyX⟩ := Finset.not_subset.mp hout
  simp only [Finset.mem_singleton] at hx hyC
  have hxv : x = v := hx.1
  subst x
  subst y
  exact hyX hx.2

private lemma join_parent_double {G : Network} {r d : ℕ} {L : ℚ} {b : ℕ → ℕ} {t : ℕ}
    {c : Construction} (F : GuideFacts G r d L b t c) {j : JoinGuide} (hj : j ∈ c.joins)
    {u : ℕ} {A : Finset ℕ} (hp : (u, A) ∈ j.edges) (hA : A ∈ j.children) :
    2 * A.card ≤ j.parent.card := by
  have hl := (F.joins j hj).1
  have hset : A ∈ (j.edges.map Prod.snd).toFinset :=
    List.mem_toFinset.mpr (List.mem_map.mpr ⟨(u, A), hp, rfl⟩)
  rw [hl.2.2.2.2.2.2.1] at hset
  have hne : A ≠ j.heavy := by
    intro heq
    subst A
    exact (Finset.mem_sdiff.mp hset).2 (Finset.mem_singleton_self _)
  have hd : Disjoint A j.heavy := hl.2.1.2.2 A hA j.heavy hl.2.2.1 hne
  have hunion : A ∪ j.heavy ⊆ j.parent := by
    intro x hx
    rcases Finset.mem_union.mp hx with h | h
    · exact child_subset_parent hl.2.1 hA h
    · exact child_subset_parent hl.2.1 hl.2.2.1 h
  have hcard : A.card + j.heavy.card ≤ j.parent.card := by
    rw [← Finset.card_union_of_disjoint hd]
    exact Finset.card_le_card hunion
  have hm := hl.2.2.2.1 A hA
  omega

private lemma target_disjoint_or_double {G : Network} {r d : ℕ} {L : ℚ} {b : ℕ → ℕ} {t : ℕ}
    {c : Construction} (F : GuideFacts G r d L b t c) {e f : TargetedGuideEdge}
    (he : e ∈ c.targetedGuide G ((L : ℝ) / (4 * d)))
    (hf : f ∈ c.targetedGuide G ((L : ℝ) / (4 * d))) (hne : e.target ≠ f.target) :
    Disjoint e.target f.target ∨ 2 * e.target.card ≤ f.target.card ∨
      2 * f.target.card ≤ e.target.card := by
  by_cases hx : (e.target ∩ f.target).Nonempty
  swap
  · left
    apply Finset.disjoint_left.mpr
    intro x hxe hxf
    exact hx ⟨x, Finset.mem_inter.mpr ⟨hxe, hxf⟩⟩
  obtain ⟨x, hx⟩ := hx
  rw [Finset.mem_inter] at hx
  rcases target_origin F he with ⟨j, hj, i, hi, u, hp, hAi, hAc, hP⟩ | hAf
  · rcases target_origin F hf with ⟨j', hj', k, hk, u', hp', hBk, hBc, hP'⟩ | hBf
    · rcases lt_trichotomy i k with hik | heq | hki
      · right; left
        have hpsub : j.parent ⊆ f.target := part_laminar F (by omega) (by omega) hP hBk
          ⟨x, Finset.mem_inter.mpr ⟨child_subset_parent (F.joins j hj).1.2.1 hAc hx.1, hx.2⟩⟩
        exact (join_parent_double F hj hp hAc).trans (Finset.card_le_card hpsub)
      · subst k
        exact False.elim (hne (part_eq_of_intersects (F.parts i (by omega)) hAi hBk
          ⟨x, Finset.mem_inter.mpr hx⟩))
      · right; right
        have hpsub : j'.parent ⊆ e.target := part_laminar F (by omega) (by omega) hP' hAi
          ⟨x, Finset.mem_inter.mpr ⟨child_subset_parent (F.joins j' hj').1.2.1 hBc hx.2, hx.1⟩⟩
        exact (join_parent_double F hj' hp' hBc).trans (Finset.card_le_card hpsub)
    · right; left
      have hpsub : j.parent ⊆ f.target := part_laminar F (by omega) le_rfl hP hBf
        ⟨x, Finset.mem_inter.mpr ⟨child_subset_parent (F.joins j hj).1.2.1 hAc hx.1, hx.2⟩⟩
      exact (join_parent_double F hj hp hAc).trans (Finset.card_le_card hpsub)
  · rcases target_origin F hf with ⟨j, hj, k, hk, u, hp, hBk, hBc, hP⟩ | hBf
    · right; right
      have hpsub : j.parent ⊆ e.target := part_laminar F (by omega) le_rfl hP hAf
        ⟨x, Finset.mem_inter.mpr ⟨child_subset_parent (F.joins j hj).1.2.1 hBc hx.2, hx.1⟩⟩
      exact (join_parent_double F hj hp hBc).trans (Finset.card_le_card hpsub)
    · exact False.elim (hne (part_eq_of_intersects (F.parts c.rounds le_rfl) hAf hBf
        ⟨x, Finset.mem_inter.mpr hx⟩))

private lemma guide_targets_nodup {G : Network} {r d : ℕ} {L : ℚ} {b : ℕ → ℕ} {t : ℕ}
    {c : Construction} (F : GuideFacts G r d L b t c) :
    ((c.targetedGuide G ((L : ℝ) / (4 * d))).map TargetedGuideEdge.target).Nodup := by
  classical
  have hclash : ∀ j₁ ∈ c.joins, ∀ j₂ ∈ c.joins, ∀ C,
      C ∈ j₁.edges.map Prod.snd → C ∈ j₂.edges.map Prod.snd → j₁ = j₂ := by
    intro j₁ hj₁ j₂ hj₂ C hC₁ hC₂
    obtain ⟨⟨u₁, C⟩, hp₁, rfl⟩ := List.mem_map.mp hC₁
    obtain ⟨⟨u₂, C⟩, hp₂, rfl⟩ := List.mem_map.mp hC₂
    obtain ⟨hl₁, i₁, hi₁, hP₁, hnew₁, hchildren₁⟩ := F.joins j₁ hj₁
    obtain ⟨hl₂, i₂, hi₂, hP₂, hnew₂, hchildren₂⟩ := F.joins j₂ hj₂
    have hs₁ : C ∈ (j₁.edges.map Prod.snd).toFinset :=
      List.mem_toFinset.mpr (List.mem_map.mpr ⟨(u₁, C), hp₁, rfl⟩)
    have hs₂ : C ∈ (j₂.edges.map Prod.snd).toFinset :=
      List.mem_toFinset.mpr (List.mem_map.mpr ⟨(u₂, C), hp₂, rfl⟩)
    rw [hl₁.2.2.2.2.2.2.1] at hs₁
    rw [hl₂.2.2.2.2.2.2.1] at hs₂
    have hc₁ := (Finset.mem_sdiff.mp hs₁).1
    have hc₂ := (Finset.mem_sdiff.mp hs₂).1
    have hp₁part : C ∈ c.partitions i₁ := by rw [hchildren₁] at hc₁; exact (Finset.mem_filter.mp hc₁).1
    have hp₂part : C ∈ c.partitions i₂ := by rw [hchildren₂] at hc₂; exact (Finset.mem_filter.mp hc₂).1
    have hsub₁ := child_subset_parent hl₁.2.1 (Finset.mem_sdiff.mp hs₁).1
    have hsub₂ := child_subset_parent hl₂.2.1 (Finset.mem_sdiff.mp hs₂).1
    have hlt₁ := child_card_lt hl₁.1 hl₁.2.1 (Finset.mem_sdiff.mp hs₁).1
    have hlt₂ := child_card_lt hl₂.1 hl₂.2.1 (Finset.mem_sdiff.mp hs₂).1
    obtain ⟨x, hx⟩ := part_nonempty (F.parts i₁ (by omega)) hp₁part
    have hit₁ : (j₁.parent ∩ C).Nonempty := ⟨x, Finset.mem_inter.mpr ⟨hsub₁ hx, hx⟩⟩
    have hit₂ : (j₂.parent ∩ C).Nonempty := ⟨x, Finset.mem_inter.mpr ⟨hsub₂ hx, hx⟩⟩
    have hi : i₁ = i₂ := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · have hs : j₁.parent ⊆ C := part_laminar F (by omega) (by omega) hP₁ hp₂part hit₁
        exact (not_le_of_gt hlt₁) (Finset.card_le_card hs)
      · have hs : j₂.parent ⊆ C := part_laminar F (by omega) (by omega) hP₂ hp₁part hit₂
        exact (not_le_of_gt hlt₂) (Finset.card_le_card hs)
    subst i₂
    have hp : j₁.parent = j₂.parent := part_eq_of_intersects (F.parts (i₁ + 1) (by omega))
      hP₁ hP₂ ⟨x, Finset.mem_inter.mpr ⟨hsub₁ hx, hsub₂ hx⟩⟩
    have hbase : c.joins.Nodup := F.joinsNodup.of_map _
    have hinj := (List.nodup_map_iff_inj_on hbase).mp F.joinsNodup
    exact hinj j₁ hj₁ j₂ hj₂ hp
  have hcross : ∀ j ∈ c.joins, ∀ C, C ∈ j.edges.map Prod.snd →
      C ∈ c.partitions c.rounds → False := by
    intro j hj C hC hfinal
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hC
    obtain ⟨hl, i, hi, hP, hnew, hchildren⟩ := F.joins j hj
    have hs : p.2 ∈ (j.edges.map Prod.snd).toFinset := List.mem_toFinset.mpr hC
    rw [hl.2.2.2.2.2.2.1] at hs
    have hchild := (Finset.mem_sdiff.mp hs).1
    have hpart : p.2 ∈ c.partitions i := by rw [hchildren] at hchild; exact (Finset.mem_filter.mp hchild).1
    have hsubchild := child_subset_parent hl.2.1 (Finset.mem_sdiff.mp hs).1
    obtain ⟨x, hx⟩ := part_nonempty (F.parts i (by omega)) hpart
    have hsub : j.parent ⊆ p.2 := part_laminar F (by omega) le_rfl hP hfinal
      ⟨x, Finset.mem_inter.mpr ⟨hsubchild hx, hx⟩⟩
    have hlt := child_card_lt hl.1 hl.2.1 (Finset.mem_sdiff.mp hs).1
    exact (not_le_of_gt hlt) (Finset.card_le_card hsub)
  have hbase : c.joins.Nodup := F.joinsNodup.of_map _
  have hJ : (c.joins.flatMap fun j => j.edges.map Prod.snd).Nodup := by
    rw [List.nodup_flatMap]
    constructor
    · intro j hj
      exact (F.joins j hj).1.2.2.2.2.2.1
    · apply (List.nodup_iff_pairwise_ne.mp hbase).imp_of_mem
      intro j₁ j₂ hj₁ hj₂ hne
      dsimp [Function.onFun]
      rw [List.disjoint_left]
      intro C hC₁ hC₂
      exact hne (hclash j₁ hj₁ j₂ hj₂ C hC₁ hC₂)
  have hD : ((c.finalSources G ((L : ℝ) / (4 * d))).toList.map (fun C => C)).Nodup := by
    simpa using (c.finalSources G ((L : ℝ) / (4 * d))).nodup_toList
  have hJF : List.Disjoint (c.joins.flatMap fun j => j.edges.map Prod.snd)
      (c.finalEdges.map Prod.snd) := by
    rw [List.disjoint_left]
    intro C hC hCf
    obtain ⟨j, hj, hCj⟩ := List.mem_flatMap.mp hC
    have hpart : C ∈ c.partitions c.rounds := by
      have hs : C ∈ (c.finalEdges.map Prod.snd).toFinset := List.mem_toFinset.mpr hCf
      rw [F.finalSet] at hs
      exact (Finset.mem_sdiff.mp hs).1
    exact hcross j hj C hCj hpart
  have hJFD : List.Disjoint
      ((c.joins.flatMap fun j => j.edges.map Prod.snd) ++ c.finalEdges.map Prod.snd)
      ((c.finalSources G ((L : ℝ) / (4 * d))).toList.map (fun C => C)) := by
    rw [List.disjoint_left]
    intro C hC hCd
    have hCs : C ∈ c.finalSources G ((L : ℝ) / (4 * d)) := by simpa using hCd
    rw [List.mem_append] at hC
    rcases hC with hC | hC
    · obtain ⟨j, hj, hCj⟩ := List.mem_flatMap.mp hC
      exact hcross j hj C hCj (Finset.mem_filter.mp hCs).1
    · have hs : C ∈ (c.finalEdges.map Prod.snd).toFinset := List.mem_toFinset.mpr hC
      rw [F.finalSet] at hs
      exact (Finset.mem_sdiff.mp hs).2 hCs
  have hJF' := (hJ.append F.finalNodup hJF).append hD hJFD
  simpa [Construction.targetedGuide, List.map_append, List.map_flatMap,
    List.map_map, Function.comp_def] using hJF'

private lemma chosen_weight_le_cut {V : Finset ℕ} {G : Network} (hG : G.Valid)
    (X : Finset ℕ) (S : Parts) (u : Finset ℕ → ℕ)
    (hSsub : ∀ A ∈ S, A ⊆ V) (hu : ∀ A ∈ S, u A ∈ A ∧ u A ∉ X)
    (hdisj : ∀ A ∈ S, ∀ B ∈ S, A ≠ B → Disjoint A B) :
    ∑ A ∈ S, weight G {u A} (A ∩ X) ≤ weight G (V \ X) X := by
  classical
  unfold weight
  generalize hGa : G.arcs = es
  have hvalid : ∀ e ∈ es, 0 ≤ e.capacity := by
    intro e he
    rw [← hGa] at he
    exact (hG e he).2.2
  clear hGa
  induction es with
  | nil => simp
  | cons e es ih =>
      have ht : ∀ a ∈ es, 0 ≤ a.capacity := by intro a ha; exact hvalid a (by simp [ha])
      specialize ih ht
      simp only [List.map_cons, List.sum_cons]
      rw [Finset.sum_add_distrib]
      apply add_le_add _ ih
      by_cases he : e.tail ∈ V \ X ∧ e.head ∈ X
      · rw [if_pos he]
        by_cases hex : ∃ A ∈ S, e.tail = u A ∧ e.head ∈ A ∩ X
        · obtain ⟨A, hA, hAe⟩ := hex
          rw [Finset.sum_eq_single A]
          · simp only [Finset.mem_singleton]
            rw [if_pos hAe]
          · intro B hB hBA
            simp only [Finset.mem_singleton]
            rw [if_neg]
            intro hBe
            have hne : A ≠ B := fun h => hBA h.symm
            have hd := hdisj A hA B hB hne
            have hxA : e.head ∈ A ∩ X := hAe.2
            have hxB : e.head ∈ B ∩ X := hBe.2
            rw [Finset.mem_inter] at hxA hxB
            exact (Finset.disjoint_left.mp hd hxA.1) hxB.1
          · intro hAn
            exact False.elim (hAn hA)
        · have hz : (∑ B ∈ S, if e.tail ∈ ({u B} : Finset ℕ) ∧
              e.head ∈ B ∩ X then e.capacity else 0) = 0 := by
            apply Finset.sum_eq_zero
            intro B hB
            simp only [Finset.mem_singleton]
            rw [if_neg]
            intro hno
            exact hex ⟨B, hB, hno⟩
          rw [hz]
          exact hvalid e (by simp)
      · have hz : (∑ A ∈ S, if e.tail ∈ ({u A} : Finset ℕ) ∧
            e.head ∈ A ∩ X then e.capacity else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro A hA
          simp only [Finset.mem_singleton]
          rw [if_neg]
          intro hcond
          have hu' := hu A hA
          have htail : e.tail ∈ V \ X := by
            rw [hcond.1]
            exact Finset.mem_sdiff.mpr ⟨hSsub A hA hu'.1, hu'.2⟩
          exact he ⟨htail, (Finset.mem_inter.mp hcond.2).2⟩
        rw [if_neg he, hz]

private lemma length_partition {α : Type*} [DecidableEq α] (l : List α)
    (cl : α → ℕ) (K : ℕ) (hcl : ∀ a ∈ l, 1 ≤ cl a ∧ cl a ≤ K) :
    l.length = ∑ k ∈ Finset.Icc 1 K, (l.filter (fun a => cl a = k)).length := by
  induction l with
  | nil => simp
  | cons a l ih =>
      have ha := hcl a (by simp)
      have hl : ∀ b ∈ l, 1 ≤ cl b ∧ cl b ≤ K := by intro b hb; exact hcl b (by simp [hb])
      simp only [List.length_cons]
      rw [ih hl]
      have hpoint : ∀ k ∈ Finset.Icc 1 K, ((a :: l).filter (fun b => cl b = k)).length =
          (if cl a = k then 1 else 0) + (l.filter (fun b => cl b = k)).length := by
        intro k hk
        by_cases h : cl a = k
        · simp [h, Nat.add_comm]
        · simp [h]
      rw [Finset.sum_congr rfl hpoint, Finset.sum_add_distrib]
      simp only [Finset.sum_ite_eq, Finset.mem_Icc]
      simp [ha.1, ha.2, Nat.add_comm]

private lemma log_monotone {a b : ℕ} (hab : a ≤ b) (ha : a ≠ 0) : Nat.log2 a ≤ Nat.log2 b := by
  have hb : b ≠ 0 := by omega
  by_contra hn
  have hlt : Nat.log2 b < Nat.log2 a := by omega
  have hbpow : b < 2 ^ Nat.log2 a := (Nat.log2_lt hb).mp hlt
  have hapow : 2 ^ Nat.log2 a ≤ a := Nat.log2_self_le ha
  omega

private lemma log_two_mul_le {a b : ℕ} (ha : a ≠ 0) (hab : 2 * a ≤ b) :
    Nat.log2 a + 1 ≤ Nat.log2 b := by
  have hmono : Nat.log2 (2 * a) ≤ Nat.log2 b := log_monotone hab (by omega)
  rwa [Nat.log2_two_mul ha] at hmono

private lemma mixed_straddle {e : TargetedGuideEdge} {X : Finset ℕ}
    (h : e.tail ∉ X ∧ e.head ∈ X ∧ ¬e.target ⊆ X) (hhead : e.head ∈ e.target) :
    (e.target ∩ X).Nonempty ∧ ¬e.target ⊆ X :=
  ⟨⟨e.head, Finset.mem_inter.mpr ⟨hhead, h.2.1⟩⟩, h.2.2⟩

private lemma classified_bound {G : Network} {r d : ℕ} {L : ℚ} {b : ℕ → ℕ} {t : ℕ}
    {c : Construction} (F : GuideFacts G r d L b t c) (hG : G.Valid) (X : Finset ℕ)
    (cl : TargetedGuideEdge → ℕ) (K : ℕ) (hτ : 0 < ((L : ℝ) / (4 * d)))
    (hbounds : ∀ e ∈ (c.targetedGuide G ((L : ℝ) / (4 * d))).filter
      (fun e => e.tail ∉ X ∧ e.head ∈ X ∧ ¬e.target ⊆ X), 1 ≤ cl e ∧ cl e ≤ K)
    (hdisj : ∀ e ∈ (c.targetedGuide G ((L : ℝ) / (4 * d))).filter
      (fun e => e.tail ∉ X ∧ e.head ∈ X ∧ ¬e.target ⊆ X),
      ∀ f ∈ (c.targetedGuide G ((L : ℝ) / (4 * d))).filter
      (fun e => e.tail ∉ X ∧ e.head ∈ X ∧ ¬e.target ⊆ X),
      cl e = cl f → e.target ≠ f.target → Disjoint e.target f.target) :
    (mixedTargetEntries c G ((L : ℝ) / (4 * d)) X : ℝ) ≤
      (K : ℝ) * cut G X / ((L : ℝ) / (4 * d)) := by
  classical
  let guide := c.targetedGuide G ((L : ℝ) / (4 * d))
  let mixed := guide.filter (fun e => e.tail ∉ X ∧ e.head ∈ X ∧ ¬e.target ⊆ X)
  have hAll : (guide.map TargetedGuideEdge.target).Nodup := guide_targets_nodup F
  have hclass : ∀ k ∈ Finset.Icc 1 K,
      ((mixed.filter (fun e => cl e = k)).length : ℝ) * ((L : ℝ) / (4 * d)) ≤ cut G X := by
    intro k hk
    let l := mixed.filter (fun e => cl e = k)
    let S := (l.map TargetedGuideEdge.target).toFinset
    have hlsub : l.Sublist guide := List.filter_sublist.trans List.filter_sublist
    have hln : (l.map TargetedGuideEdge.target).Nodup := (hlsub.map _).nodup hAll
    have hlevel : ∀ A ∈ S, ∃ i ≤ c.rounds, A ∈ c.partitions i := by
      intro A hA
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hA)
      have heg : e ∈ guide := hlsub.subset he
      rcases target_origin F heg with ⟨j, hj, i, hi, u, hp, hAi, hAc, hP⟩ | hA
      · exact ⟨i, by omega, hAi⟩
      · exact ⟨c.rounds, le_rfl, hA⟩
    have hSsub : ∀ A ∈ S, A ⊆ G.vertices := by
      intro A hA
      obtain ⟨i, hi, hAi⟩ := hlevel A hA
      exact part_subset (F.parts i hi) hAi
    have hSdisj : ∀ A ∈ S, ∀ B ∈ S, A ≠ B → Disjoint A B := by
      intro A hA B hB hne
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hA)
      obtain ⟨f, hf, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hB)
      have he' := List.mem_filter.mp he
      have hf' := List.mem_filter.mp hf
      apply hdisj e he'.1 f hf'.1
      · have hcek : cl e = k := of_decide_eq_true he'.2
        have hcfk : cl f = k := of_decide_eq_true hf'.2
        omega
      · exact hne
    have hentries : ∀ A ∈ S, ∃ u, (u ∈ A ∧ u ∉ X) ∧
        ((L : ℝ) / (4 * d)) < weight G {u} (A ∩ X) := by
      intro A hA
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hA)
      have heg : e ∈ guide := hlsub.subset he
      have hem : e ∈ mixed := (List.mem_filter.mp he).1
      have hstr := mixed_straddle (of_decide_eq_true (List.mem_filter.mp hem).2) (target_head F heg)
      rcases target_origin F heg with ⟨j, hj, i, hi, u, hp, hAi, hAc, hP⟩ | hAi
      · obtain ⟨v, hvA, hvX, hcharge⟩ := mixed_part_charge_aux F hG X e.target.card
          e.target i rfl (by omega) hAi hstr.1 hstr.2
        exact ⟨v, ⟨hvA, hvX⟩, hcharge⟩
      · obtain ⟨v, hvA, hvX, hcharge⟩ := mixed_part_charge_aux F hG X e.target.card
          e.target c.rounds rfl le_rfl hAi hstr.1 hstr.2
        exact ⟨v, ⟨hvA, hvX⟩, hcharge⟩
    let u : Finset ℕ → ℕ := fun A => if h : A ∈ S then (hentries A h).choose else 0
    have hu : ∀ A ∈ S, u A ∈ A ∧ u A ∉ X := by
      intro A hA
      dsimp [u]
      rw [dif_pos hA]
      exact (hentries A hA).choose_spec.1
    have hcharge : ∀ A ∈ S, ((L : ℝ) / (4 * d)) < weight G {u A} (A ∩ X) := by
      intro A hA
      dsimp [u]
      rw [dif_pos hA]
      exact (hentries A hA).choose_spec.2
    change (l.length : ℝ) * ((L : ℝ) / (4 * d)) ≤ cut G X
    calc
      (l.length : ℝ) * ((L : ℝ) / (4 * d)) = ∑ A ∈ S, ((L : ℝ) / (4 * d)) := by
        rw [Finset.sum_const, List.toFinset_card_of_nodup hln, nsmul_eq_mul]
        simp
      _ ≤ ∑ A ∈ S, weight G {u A} (A ∩ X) :=
        Finset.sum_le_sum (fun A hA => (hcharge A hA).le)
      _ ≤ weight G (G.vertices \ X) X := chosen_weight_le_cut hG X S u hSsub hu hSdisj
      _ = cut G X := rfl
  have hmul : (mixed.length : ℝ) * ((L : ℝ) / (4 * d)) ≤ (K : ℝ) * cut G X := by
    rw [length_partition mixed cl K hbounds]
    push_cast
    calc
      (∑ k ∈ Finset.Icc 1 K, ((mixed.filter (fun e => cl e = k)).length : ℝ)) *
          ((L : ℝ) / (4 * d)) = ∑ k ∈ Finset.Icc 1 K,
          (((mixed.filter (fun e => cl e = k)).length : ℝ) * ((L : ℝ) / (4 * d))) := by
            rw [Finset.sum_mul]
      _ ≤ ∑ k ∈ Finset.Icc 1 K, cut G X := Finset.sum_le_sum hclass
      _ = (K : ℝ) * cut G X := by simp [Nat.card_Icc]
  change (mixed.length : ℝ) ≤ (K : ℝ) * cut G X / ((L : ℝ) / (4 * d))
  calc
    (mixed.length : ℝ) = (mixed.length : ℝ) * ((L : ℝ) / (4 * d)) /
        ((L : ℝ) / (4 * d)) := by rw [mul_div_assoc, div_self (ne_of_gt hτ), mul_one]
    _ ≤ ((K : ℝ) * cut G X) / ((L : ℝ) / (4 * d)) := div_le_div_of_nonneg_right hmul hτ.le
    _ = (K : ℝ) * cut G X / ((L : ℝ) / (4 * d)) := rfl

theorem solution (G : Network) (r d : ℕ) (L : ℚ) (b : ℕ → ℕ) (t : ℕ)
    (c : Construction) (X : Finset ℕ)
    (hG : Prepared G r) (hd : 1 ≤ d) (hdn : d ≤ G.vertices.card)
    (hL : 0 < L) (hlower : RootLowerBound G r L)
    (hc : LegalConstruction G r d L b t c)
    (hX : X ⊆ G.vertices \ (c.earlyProbes G r ((L : ℝ) / (4 * d)) ∪ {r})) :
    (mixedTargetEntries c G ((L : ℝ) / (4 * d)) X : ℝ) ≤
      (Nat.log2 G.vertices.card) * cut G X / ((L : ℝ) / (4 * d)) := by
  classical
  let F := guideFacts hc
  let guide := c.targetedGuide G ((L : ℝ) / (4 * d))
  let mixed := guide.filter (fun e => e.tail ∉ X ∧ e.head ∈ X ∧ ¬e.target ⊆ X)
  have hτ : 0 < ((L : ℝ) / (4 * d)) := by
    have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
    have hL' : (0 : ℝ) < L := by exact_mod_cast hL
    positivity
  have hinfo : ∀ e ∈ mixed, ∃ i, 1 ≤ i ∧ i ≤ c.rounds ∧
      e.target ∈ c.partitions i ∧ 2 ≤ e.target.card := by
    intro e he
    have heg : e ∈ guide := (List.mem_filter.mp he).1
    have hstr := mixed_straddle (of_decide_eq_true (List.mem_filter.mp he).2) (target_head F heg)
    have hne1 := not_straddling_singleton hstr.1 hstr.2
    have hnonempty : e.target.Nonempty := by
      obtain ⟨x, hx⟩ := hstr.1
      exact ⟨x, (Finset.mem_inter.mp hx).1⟩
    have hcard : 2 ≤ e.target.card := by have := Finset.card_pos.mpr hnonempty; omega
    rcases target_origin F heg with ⟨j, hj, i, hi, u, hp, hAi, hAc, hP⟩ | hAf
    · refine ⟨i, ?_, by omega, hAi, hcard⟩
      by_contra hi0
      have hizero : i = 0 := by omega
      subst i
      rw [F.initial] at hAi
      obtain ⟨v, hv, hsingle⟩ := Finset.mem_image.mp hAi
      apply hne1
      rw [← hsingle]
      simp
    · exact ⟨c.rounds, F.rounds, le_rfl, hAf, hcard⟩
  have hbounds : ∀ e ∈ mixed, 1 ≤ Nat.log2 e.target.card ∧
      Nat.log2 e.target.card ≤ Nat.log2 G.vertices.card := by
    intro e he
    obtain ⟨i, hi1, hiR, hpart, hcard⟩ := hinfo e he
    constructor
    · have hmono := log_monotone hcard (by decide : (2 : ℕ) ≠ 0)
      simpa using hmono
    · apply log_monotone (Finset.card_le_card (part_subset (F.parts i hiR) hpart))
      omega
  apply classified_bound F hG.1 X (fun e => Nat.log2 e.target.card) (Nat.log2 G.vertices.card) hτ hbounds
  intro e he f hf hrank hne
  have heg : e ∈ guide := (List.mem_filter.mp he).1
  have hfg : f ∈ guide := (List.mem_filter.mp hf).1
  obtain ⟨i, hi1, hiR, hip, hicard⟩ := hinfo e he
  obtain ⟨j, hj1, hjR, hjp, hjcard⟩ := hinfo f hf
  rcases target_disjoint_or_double F heg hfg hne with hd | hdouble | hdouble
  · exact hd
  · have hlog := log_two_mul_le (show e.target.card ≠ 0 by omega) hdouble
    omega
  · have hlog := log_two_mul_le (show f.target.card ≠ 0 by omega) hdouble
    omega
