-- Prove2me | solution 1 for BudgetClock.NonMonotone.lemma_7
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T03:59:30.831994+00:00
-- url     : https://prove2.me/submissions/ef259c95-c9ea-42c9-8d68-3415691dc2b8

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_BudgetClock_NonMonotone_Mechanism
import Theorems.Thm_BudgetClock_NonMonotone_corollary_1

namespace BCNMInv
open BudgetClock.NonMonotone BudgetClock.Monotone

theorem sublist_dropLast {α : Type} {T L : List α} (h : T.Sublist L) :
    T.dropLast.Sublist L.dropLast := by
  have h1 := (h.reverse).tail
  rw [List.tail_reverse, List.tail_reverse] at h1
  simpa using h1.reverse

theorem listCost_sublist_le {n : ℕ} {p : Fin n → ℝ} {T L : List (Fin n)} (h : T.Sublist L)
    (hp : ∀ i ∈ L, 0 ≤ p i) : listCost p T ≤ listCost p L := by
  unfold listCost
  apply (h.map p).sum_le_sum
  intro a ha
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 ha
  exact hp i hi

theorem listCost_congr {n : ℕ} {p p' : Fin n → ℝ} {T : List (Fin n)}
    (h : ∀ i ∈ T, p' i = p i) : listCost p' T = listCost p T := by
  unfold listCost
  rw [List.map_congr_left h]

theorem listCost_append_single {n : ℕ} (p : Fin n → ℝ) (T : List (Fin n)) (i : Fin n) :
    listCost p (T ++ [i]) = listCost p T + p i := by
  simp [listCost]

/-- Good list at prices `p`: what is needed at the end for budget feasibility and pruning. -/
def Good {n : ℕ} (v : Finset (Fin n) → ℝ) (B : ℝ) (p : Fin n → ℝ) (L : List (Fin n)) : Prop :=
  L.Nodup ∧ (∀ i ∈ L, 0 ≤ p i) ∧
    ∀ T, T.Sublist L → listCost p T.dropLast ≤ B ∧
      (B < listCost p T → ∀ j, 2 * v {j} ≤ v T.toFinset)

/-- In-phase invariant for a list being built with target `τ`. -/
def InPh {n : ℕ} (v : Finset (Fin n) → ℝ) (B : ℝ) (p : Fin n → ℝ) (τ : ℝ) (L : List (Fin n)) :
    Prop :=
  L.Nodup ∧ (∀ i ∈ L, 0 ≤ p i) ∧
    (∀ T, T.Sublist L → listCost p T ≤ (v T.toFinset - v ∅) * B / τ) ∧
    (L ≠ [] → v L.dropLast.toFinset < τ)

theorem Good.sublist {n : ℕ} {v : Finset (Fin n) → ℝ} {B : ℝ} {p : Fin n → ℝ}
    {L T : List (Fin n)} (h : Good v B p L) (hT : T.Sublist L) : Good v B p T :=
  ⟨h.1.sublist hT, fun i hi => h.2.1 i (hT.subset hi), fun T' hT' => h.2.2 T' (hT'.trans hT)⟩

theorem Good.congr {n : ℕ} {v : Finset (Fin n) → ℝ} {B : ℝ} {p p' : Fin n → ℝ}
    {L : List (Fin n)} (h : Good v B p L) (hp : ∀ i ∈ L, p' i = p i) : Good v B p' L := by
  refine ⟨h.1, fun i hi => by rw [hp i hi]; exact h.2.1 i hi, fun T hT => ?_⟩
  have h1 : listCost p' T = listCost p T :=
    listCost_congr (fun i hi => hp i (hT.subset hi))
  have h2 : listCost p' T.dropLast = listCost p T.dropLast :=
    listCost_congr (fun i hi => hp i (hT.subset ((List.dropLast_sublist T).subset hi)))
  rw [h1, h2]; exact h.2.2 T hT

theorem InPh.congr {n : ℕ} {v : Finset (Fin n) → ℝ} {B τ : ℝ} {p p' : Fin n → ℝ}
    {L : List (Fin n)} (h : InPh v B p τ L) (hp : ∀ i ∈ L, p' i = p i) : InPh v B p' τ L := by
  refine ⟨h.1, fun i hi => by rw [hp i hi]; exact h.2.1 i hi, fun T hT => ?_, h.2.2.2⟩
  rw [listCost_congr (fun i hi => hp i (hT.subset hi))]; exact h.2.2.1 T hT

theorem InPh.nil {n : ℕ} (v : Finset (Fin n) → ℝ) (B : ℝ) (p : Fin n → ℝ) (τ : ℝ) :
    InPh v B p τ [] := by
  refine ⟨List.nodup_nil, by simp, fun T hT => ?_, by simp⟩
  rw [List.sublist_nil] at hT; subst hT; simp [listCost]

theorem InPh.good {n : ℕ} {v : Finset (Fin n) → ℝ} (hv : ∀ S, 0 ≤ v S) {B τ : ℝ} (hB : 0 < B)
    {p : Fin n → ℝ} {L : List (Fin n)} (h : InPh v B p τ L) (hτ : ∀ j, 2 * v {j} ≤ τ)
    (hτ0 : 0 ≤ τ) : Good v B p L := by
  refine ⟨h.1, h.2.1, fun T hT => ⟨?_, ?_⟩⟩
  · have hle : listCost p T.dropLast ≤ listCost p L.dropLast :=
      listCost_sublist_le (sublist_dropLast hT)
        (fun i hi => h.2.1 i ((List.dropLast_sublist L).subset hi))
    by_cases hL : L = []
    · subst hL
      have : T = [] := List.sublist_nil.1 hT
      subst this; simp [listCost]; exact hB.le
    · have h1 := h.2.2.2 hL
      have hτp : 0 < τ := lt_of_le_of_lt (hv _) h1
      have h2 := h.2.2.1 L.dropLast (List.dropLast_sublist L)
      have h3 : (v L.dropLast.toFinset - v ∅) * B / τ ≤ B := by
        rw [div_le_iff₀ hτp]
        have := hv ∅
        nlinarith
      linarith
  · intro hlt j
    have h2 := h.2.2.1 T hT
    rcases eq_or_lt_of_le hτ0 with h0 | hτp
    · rw [← h0] at h2; simp at h2; linarith
    · have h3 : B < (v T.toFinset - v ∅) * B / τ := lt_of_lt_of_le hlt h2
      rw [lt_div_iff₀ hτp] at h3
      have := hv ∅
      have h4 : τ < v T.toFinset - v ∅ := by
        by_contra hc; push Not at hc; nlinarith
      linarith [hτ j]

theorem good_of_length_le_one {n : ℕ} (v : Finset (Fin n) → ℝ) {B : ℝ} (hB : 0 < B)
    (p : Fin n → ℝ) (L : List (Fin n)) (hL : L.length ≤ 1) (hp : ∀ i ∈ L, 0 ≤ p i ∧ p i ≤ B) :
    Good v B p L := by
  refine ⟨?_, fun i hi => (hp i hi).1, fun T hT => ⟨?_, ?_⟩⟩
  · match L, hL with
    | [], _ => exact List.nodup_nil
    | [a], _ => exact List.nodup_singleton a
  · have : T.length ≤ 1 := le_trans hT.length_le hL
    match T, this with
    | [], _ => simp [listCost]; exact hB.le
    | [a], _ => simp [listCost]; exact hB.le
  · intro hlt
    have : T.length ≤ 1 := le_trans hT.length_le hL
    exfalso
    match T, this, hT with
    | [], _, _ => simp [listCost] at hlt; linarith
    | [a], _, hT' =>
      simp [listCost] at hlt
      have := (hp a (hT'.subset (by simp))).2
      linarith

/-! Submodularity facts. -/

theorem submod_marg {n : ℕ} {v : Finset (Fin n) → ℝ}
    (hsub : NonmonotoneSubmod.Shared.Submodular v) {A C : Finset (Fin n)} (hAC : A ⊆ C)
    {i : Fin n} (hi : i ∉ C) : v (C ∪ {i}) - v C ≤ v (A ∪ {i}) - v A := by
  have h := hsub (A ∪ {i}) C
  have e1 : A ∪ {i} ∪ C = C ∪ {i} := by
    ext x; simp only [Finset.mem_union, Finset.mem_singleton]
    constructor
    · rintro ((h|h)|h)
      · exact Or.inl (hAC h)
      · exact Or.inr h
      · exact Or.inl h
    · rintro (h|h)
      · exact Or.inr h
      · exact Or.inl (Or.inr h)
  have e2 : (A ∪ {i}) ∩ C = A := by
    ext x; simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_inter]
    constructor
    · rintro ⟨h|h, h'⟩
      · exact h
      · subst h; exact absurd h' hi
    · intro h; exact ⟨Or.inl h, hAC h⟩
  rw [e1, e2] at h
  linarith

theorem submod_single {n : ℕ} {v : Finset (Fin n) → ℝ}
    (hsub : NonmonotoneSubmod.Shared.Submodular v) (D : Finset (Fin n)) {a : Fin n}
    (ha : a ∉ D) : v (D ∪ {a}) + v ∅ ≤ v D + v {a} := by
  have h := hsub D {a}
  have : D ∩ {a} = ∅ := by
    ext x; simp only [Finset.mem_inter, Finset.mem_singleton, Finset.notMem_empty, iff_false]
    rintro ⟨h1, rfl⟩; exact ha h1
  rw [this] at h; exact h

/-! The mechanism's invariants. -/

theorem pickBidder_mem {n : ℕ} {v : Finset (Fin n) → ℝ} {s : State n} {i : Fin n}
    (h : pickBidder v s = some i) : i ∈ pool s := by
  unfold pickBidder at h
  simp only at h
  split_ifs at h with hM
  · cases h
    exact (Finset.mem_filter.1 (Finset.min'_mem _ hM)).1

theorem mem_pool {n : ℕ} {s : State n} {i : Fin n} (h : i ∈ pool s) :
    i ∈ s.A ∧ i ∉ s.prev1 ∧ i ∉ s.prev2 ∧ i ∉ s.cur1 ∧ i ∉ s.cur2 := by
  unfold pool at h
  simp only [Finset.mem_sdiff, Finset.mem_union, List.mem_toFinset, not_or] at h
  exact ⟨h.1, h.2.1.1.1, h.2.1.1.2, h.2.1.2, h.2.2⟩

theorem innerStep_tgt {n : ℕ} (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (B : ℝ) (s : State n)
    (i : Fin n) : (innerStep v c B s i).tgt = s.tgt := by
  unfold innerStep; simp only; split_ifs <;> rfl

theorem innerLoop_tgt {n : ℕ} (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (B : ℝ) :
    ∀ (k : ℕ) (s : State n), (innerLoop v c B k s).tgt = s.tgt := by
  intro k
  induction k with
  | zero => intro s; rfl
  | succ k ih =>
    intro s
    unfold innerLoop
    split_ifs
    · rfl
    · split
      · rfl
      · rw [ih, innerStep_tgt]

/-- Inner invariant. -/
def InnerInv {n : ℕ} (v : Finset (Fin n) → ℝ) (B : ℝ) (s : State n) : Prop :=
  Good v B s.p s.prev1 ∧ Good v B s.p s.prev2 ∧ InPh v B s.p s.tgt s.cur1 ∧
    InPh v B s.p s.tgt s.cur2 ∧ (∀ i ∈ s.cur1, i ∉ s.cur2)

theorem inPh_append {n : ℕ} {v : Finset (Fin n) → ℝ} (hv : ∀ S, 0 ≤ v S)
    (hsub : NonmonotoneSubmod.Shared.Submodular v) {B τ : ℝ} (hB : 0 < B)
    {p : Fin n → ℝ} {L : List (Fin n)} (h : InPh v B p τ L) {i : Fin n} (hi : i ∉ L)
    (hLτ : v L.toFinset < τ) (x : ℝ) (hx0 : 0 ≤ x)
    (hx : x ≤ (v (L.toFinset ∪ {i}) - v L.toFinset) * B / τ) :
    InPh v B (Function.update p i x) τ (L ++ [i]) := by
  have hτp : 0 < τ := lt_of_le_of_lt (hv _) hLτ
  have hpL : ∀ j ∈ L, Function.update p i x j = p j := by
    intro j hj; rw [Function.update_of_ne]; rintro rfl; exact hi hj
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [List.nodup_append]
    refine ⟨h.1, List.nodup_singleton i, ?_⟩
    intro a ha b hb; simp at hb; subst hb; rintro rfl; exact hi ha
  · intro j hj
    rw [List.mem_append] at hj
    rcases hj with hj | hj
    · rw [hpL j hj]; exact h.2.1 j hj
    · simp at hj; subst hj; simp; exact hx0
  · intro T hT
    obtain ⟨a, b, rfl, ha, hb⟩ := List.sublist_append_iff.1 hT
    rcases List.sublist_singleton.1 hb with rfl | rfl
    · simp only [List.append_nil]
      rw [listCost_congr (fun j hj => hpL j (ha.subset hj))]
      exact h.2.2.1 a ha
    · rw [listCost_append_single, listCost_congr (fun j hj => hpL j (ha.subset hj))]
      simp only [Function.update_self]
      have h1 := h.2.2.1 a ha
      have hsm := submod_marg hsub (by intro x hx; rw [List.mem_toFinset] at hx ⊢; exact ha.subset hx)
        (show i ∉ L.toFinset by simpa using hi)
      have e : (a ++ [i]).toFinset = a.toFinset ∪ {i} := by
        rw [List.toFinset_append]; simp
      rw [e]
      have hBτ : 0 ≤ B / τ := div_nonneg hB.le hτp.le
      rw [mul_div_assoc] at h1 hx ⊢
      nlinarith
  · intro _
    rw [List.dropLast_concat]; exact hLτ

theorem innerStep_inv {n : ℕ} {v : Finset (Fin n) → ℝ} (hv : ∀ S, 0 ≤ v S)
    (hsub : NonmonotoneSubmod.Shared.Submodular v) {c : Fin n → ℝ} (hc : ∀ i, 0 ≤ c i)
    {B : ℝ} (hB : 0 < B) {s : State n} (hs : InnerInv v B s) {i : Fin n} (hi : i ∈ pool s)
    (hlt : ¬ s.tgt ≤ max (v s.cur1.toFinset) (v s.cur2.toFinset)) :
    InnerInv v B (innerStep v c B s i) := by
  obtain ⟨hA, hp1, hp2, hc1, hc2⟩ := mem_pool hi
  push Not at hlt
  have hlt1 : v s.cur1.toFinset < s.tgt := lt_of_le_of_lt (le_max_left _ _) hlt
  have hlt2 : v s.cur2.toFinset < s.tgt := lt_of_le_of_lt (le_max_right _ _) hlt
  obtain ⟨g1, g2, i1, i2, dj⟩ := hs
  have ne : ∀ L : List (Fin n), i ∉ L → ∀ j ∈ L, ∀ x : ℝ, Function.update s.p i x j = s.p j := by
    intro L hL j hj x; rw [Function.update_of_ne]; rintro rfl; exact hL hj
  unfold innerStep
  simp only
  set m1 := marg v {i} s.cur1.toFinset with hm1
  set m2 := marg v {i} s.cur2.toFinset with hm2
  set x := min (s.p i) ((if m2 ≤ m1 then m1 else m2) * B / s.tgt) with hx
  split_ifs with hcx hm
  · -- accept into cur1
    refine ⟨g1.congr (ne _ hp1 · · x), g2.congr (ne _ hp2 · · x), ?_,
      i2.congr (ne _ hc2 · · x), ?_⟩
    · apply inPh_append hv hsub hB i1 hc1 hlt1 x (le_trans (hc i) hcx)
      have : x ≤ m1 * B / s.tgt := by rw [hx, if_pos hm]; exact min_le_right _ _
      simpa [hm1, marg, Finset.union_comm] using this
    · intro j hj
      rw [List.mem_append] at hj
      rcases hj with hj | hj
      · exact dj j hj
      · simp at hj; subst hj; exact hc2
  · -- accept into cur2
    refine ⟨g1.congr (ne _ hp1 · · x), g2.congr (ne _ hp2 · · x),
      i1.congr (ne _ hc1 · · x), ?_, ?_⟩
    · apply inPh_append hv hsub hB i2 hc2 hlt2 x (le_trans (hc i) hcx)
      have : x ≤ m2 * B / s.tgt := by rw [hx, if_neg hm]; exact min_le_right _ _
      simpa [hm2, marg, Finset.union_comm] using this
    · intro j hj hj2
      rw [List.mem_append] at hj2
      rcases hj2 with hj2 | hj2
      · exact dj j hj hj2
      · simp at hj2; subst hj2; exact hc1 hj
  · -- reject
    exact ⟨g1.congr (ne _ hp1 · · x), g2.congr (ne _ hp2 · · x),
      i1.congr (ne _ hc1 · · x), i2.congr (ne _ hc2 · · x), dj⟩

theorem innerLoop_inv {n : ℕ} {v : Finset (Fin n) → ℝ} (hv : ∀ S, 0 ≤ v S)
    (hsub : NonmonotoneSubmod.Shared.Submodular v) {c : Fin n → ℝ} (hc : ∀ i, 0 ≤ c i)
    {B : ℝ} (hB : 0 < B) : ∀ (k : ℕ) (s : State n), InnerInv v B s →
      InnerInv v B (innerLoop v c B k s) := by
  intro k
  induction k with
  | zero => intro s hs; exact hs
  | succ k ih =>
    intro s hs
    unfold innerLoop
    split_ifs with h
    · exact hs
    · split
      · exact hs
      · rename_i i hi
        exact ih _ (innerStep_inv hv hsub hc hB hs (pickBidder_mem hi) h)

/-- Outer invariant. -/
def OuterInv {n : ℕ} (v : Finset (Fin n) → ℝ) (B : ℝ) (s : State n) : Prop :=
  Good v B s.p s.prev1 ∧ Good v B s.p s.prev2 ∧ Good v B s.p s.cur1 ∧ Good v B s.p s.cur2 ∧
    (∀ i ∈ s.cur1, i ∉ s.cur2) ∧ (∀ j, v {j} ≤ s.tgt) ∧ 0 ≤ s.tgt

theorem phase_inv {n : ℕ} {v : Finset (Fin n) → ℝ} (hv : ∀ S, 0 ≤ v S)
    (hsub : NonmonotoneSubmod.Shared.Submodular v) {c : Fin n → ℝ} (hc : ∀ i, 0 ≤ c i)
    {B : ℝ} (hB : 0 < B) {s : State n} (hs : OuterInv v B s) :
    OuterInv v B (phase v c B s) := by
  obtain ⟨_, _, g1, g2, _, ht, ht0⟩ := hs
  unfold phase
  have h0 : InnerInv v B (State.mk s.A s.cur1 s.cur2 [] [] (2 * s.tgt) (s.t + 1) s.p) :=
    ⟨g1, g2, InPh.nil v B _ _, InPh.nil v B _ _, by simp⟩
  have h1 := innerLoop_inv hv hsub hc hB n _ h0
  have htg := innerLoop_tgt v c B n (State.mk s.A s.cur1 s.cur2 [] [] (2 * s.tgt) (s.t + 1) s.p)
  show OuterInv v B (innerLoop v c B n (State.mk s.A s.cur1 s.cur2 [] [] (2 * s.tgt) (s.t + 1) s.p))
  obtain ⟨a1, a2, a3, a4, a5⟩ := h1
  have hτ : ∀ j, 2 * v {j} ≤ (innerLoop v c B n
      (State.mk s.A s.cur1 s.cur2 [] [] (2 * s.tgt) (s.t + 1) s.p)).tgt := by
    intro j; rw [htg]; linarith [ht j]
  have hτ0 : 0 ≤ (innerLoop v c B n
      (State.mk s.A s.cur1 s.cur2 [] [] (2 * s.tgt) (s.t + 1) s.p)).tgt := by rw [htg]; linarith
  refine ⟨a1, a2, a3.good hv hB hτ hτ0, a4.good hv hB hτ hτ0, a5, ?_, hτ0⟩
  intro j; linarith [hτ j, hv {j}]

theorem outerStep_inv {n : ℕ} {v : Finset (Fin n) → ℝ} (hv : ∀ S, 0 ≤ v S)
    (hsub : NonmonotoneSubmod.Shared.Submodular v) {c : Fin n → ℝ} (hc : ∀ i, 0 ≤ c i)
    {B : ℝ} (hB : 0 < B) {s : State n} (hs : OuterInv v B s) :
    OuterInv v B (outerStep v c B s) := by
  unfold outerStep
  split_ifs
  · exact phase_inv hv hsub hc hB hs
  · exact hs

theorem bestSingleton_spec {n : ℕ} (v : Finset (Fin n) → ℝ) :
    (bestSingleton v).length ≤ 1 ∧ ∀ j, v {j} ≤ v (bestSingleton v).toFinset := by
  unfold bestSingleton
  simp only
  split_ifs with hM
  · refine ⟨by simp, fun j => ?_⟩
    have := (Finset.mem_filter.1 (Finset.min'_mem _ hM)).2 j
    simpa using this
  · refine ⟨by simp, fun j => ?_⟩
    exfalso
    obtain ⟨x, _, hx⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin n))
      (fun i => v {i}) ⟨j, Finset.mem_univ _⟩
    exact hM ⟨x, Finset.mem_filter.2 ⟨Finset.mem_univ _, fun j' => hx j' (Finset.mem_univ _)⟩⟩

theorem initState_inv {n : ℕ} {v : Finset (Fin n) → ℝ} (hv : ∀ S, 0 ≤ v S)
    {B : ℝ} (hB : 0 < B) : OuterInv v B (initState v B) := by
  obtain ⟨hl, hm⟩ := bestSingleton_spec v
  have gnil : Good v B (fun _ => B) ([] : List (Fin n)) :=
    good_of_length_le_one v hB _ [] (by simp) (by simp)
  refine ⟨gnil, gnil, gnil, good_of_length_le_one v hB _ _ hl (fun _ _ => ⟨hB.le, le_rfl⟩),
    by simp [initState], hm, hv _⟩

theorem phaseEnd_inv {n : ℕ} {v : Finset (Fin n) → ℝ} (hv : ∀ S, 0 ≤ v S)
    (hsub : NonmonotoneSubmod.Shared.Submodular v) {c : Fin n → ℝ} (hc : ∀ i, 0 ≤ c i)
    {B : ℝ} (hB : 0 < B) (k : ℕ) : OuterInv v B (phaseEnd v c B k) := by
  induction k with
  | zero => exact initState_inv hv hB
  | succ k ih =>
    unfold phaseEnd at ih ⊢
    rw [Function.iterate_succ_apply']
    exact outerStep_inv hv hsub hc hB ih

theorem candidates_good {n : ℕ} {v : Finset (Fin n) → ℝ} {B : ℝ}
    (usm : Finset (Fin n) → Finset (Fin n)) {s : State n} (hs : OuterInv v B s) :
    ∀ L ∈ candidates usm s, Good v B s.p L := by
  obtain ⟨g1, g2, g3, g4, _⟩ := hs
  intro L hL
  simp only [candidates, List.mem_cons, List.not_mem_nil, or_false] at hL
  rcases hL with rfl | rfl | rfl | rfl | rfl | rfl
  · exact g1
  · exact g2
  · exact g3.sublist (List.filter_sublist)
  · exact g4.sublist (List.filter_sublist)
  · exact g1.sublist (List.filter_sublist)
  · exact g2.sublist (List.filter_sublist)

theorem firstArgmax_spec {n : ℕ} (v : Finset (Fin n) → ℝ) :
    ∀ (L : List (Fin n)) (Ls : List (List (Fin n))),
      firstArgmax v (L :: Ls) ∈ L :: Ls ∧
        ∀ M ∈ L :: Ls, v M.toFinset ≤ v (firstArgmax v (L :: Ls)).toFinset := by
  intro L Ls
  induction Ls generalizing L with
  | nil => simp [firstArgmax]
  | cons L' Ls ih =>
    obtain ⟨h1, h2⟩ := ih L'
    simp only [firstArgmax]
    split_ifs with h
    · refine ⟨List.mem_cons_self, fun M hM => ?_⟩
      rcases List.mem_cons.1 hM with rfl | hM
      · exact le_rfl
      · exact le_trans (h2 M hM) h
    · push Not at h
      refine ⟨List.mem_cons_of_mem _ h1, fun M hM => ?_⟩
      rcases List.mem_cons.1 hM with rfl | hM
      · exact h.le
      · exact h2 M hM

theorem final_inv {n : ℕ} {v : Finset (Fin n) → ℝ} (hv : ∀ S, 0 ≤ v S)
    (hsub : NonmonotoneSubmod.Shared.Submodular v) {c : Fin n → ℝ} (hc : ∀ i, 0 ≤ c i)
    {B : ℝ} (hB : 0 < B) : OuterInv v B (finalState v c B) :=
  phaseEnd_inv hv hsub hc hB (n + 2)

/-- The chosen candidate `S*` (before pruning). -/
theorem chosen_spec {n : ℕ} {v : Finset (Fin n) → ℝ} (hv : ∀ S, 0 ≤ v S)
    (hsub : NonmonotoneSubmod.Shared.Submodular v) {c : Fin n → ℝ} (hc : ∀ i, 0 ≤ c i)
    {B : ℝ} (hB : 0 < B) (usm : Finset (Fin n) → Finset (Fin n)) :
    let s := finalState v c B
    let S := firstArgmax v (candidates usm s)
    Good v B s.p S ∧ ∀ L ∈ candidates usm s, v L.toFinset ≤ v S.toFinset := by
  intro s S
  have hc' : candidates usm s = s.prev1 :: (candidates usm s).tail := rfl
  obtain ⟨h1, h2⟩ := firstArgmax_spec v s.prev1 (candidates usm s).tail
  rw [← hc'] at h1 h2
  exact ⟨candidates_good usm (final_inv hv hsub hc hB) _ h1, h2⟩

theorem budget {n : ℕ} (v : Finset (Fin n) → ℝ) (hv : ∀ S, 0 ≤ v S)
    (hsub : NonmonotoneSubmod.Shared.Submodular v)
    (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i) (B : ℝ) (hB : 0 < B)
    (usm : Finset (Fin n) → Finset (Fin n)) :
    ∑ i ∈ (simultaneousIterativePruning v c B usm).1,
      (simultaneousIterativePruning v c B usm).2 i ≤ B := by
  obtain ⟨hg, _⟩ := chosen_spec hv hsub hc hB usm
  simp only [simultaneousIterativePruning, chosenSet]
  set s := finalState v c B
  set S := firstArgmax v (candidates usm s)
  split_ifs with h
  · rw [List.sum_toFinset _ (hg.1.sublist (List.dropLast_sublist S))]
    exact (hg.2.2 S (List.Sublist.refl S)).1
  · rw [List.sum_toFinset _ hg.1]
    push Not at h; exact h

theorem pruning {n : ℕ} (v : Finset (Fin n) → ℝ) (hv : ∀ S, 0 ≤ v S)
    (hsub : NonmonotoneSubmod.Shared.Submodular v)
    (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i) (B : ℝ) (hB : 0 < B)
    (usm : Finset (Fin n) → Finset (Fin n)) :
    ∀ L ∈ candidates usm (finalState v c B),
      v L.toFinset / 2 ≤ v (simultaneousIterativePruning v c B usm).1 := by
  obtain ⟨hg, hmax⟩ := chosen_spec hv hsub hc hB usm
  intro L hL
  have hLS := hmax L hL
  simp only [simultaneousIterativePruning, chosenSet]
  set s := finalState v c B
  set S := firstArgmax v (candidates usm s)
  split_ifs with h
  · have h2 := (hg.2.2 S (List.Sublist.refl S)).2 h
    have hne : S ≠ [] := by
      rintro hS; rw [hS] at h; simp [listCost] at h; linarith
    have hdec := List.dropLast_append_getLast hne
    set a := S.getLast hne
    have hnd : (S.dropLast ++ [a]).Nodup := by rw [hdec]; exact hg.1
    have ha : a ∉ S.dropLast.toFinset := by
      rw [List.nodup_append] at hnd
      intro hm
      exact hnd.2.2 a (List.mem_toFinset.1 hm) a (by simp) rfl
    have hsm := submod_single hsub S.dropLast.toFinset ha
    have e : S.toFinset = S.dropLast.toFinset ∪ {a} := by
      conv_lhs => rw [← hdec]
      rw [List.toFinset_append]; simp
    rw [← e] at hsm
    have := h2 a
    have := hv ∅
    linarith
  · have := hv L.toFinset
    linarith

end BCNMInv

namespace BCNMTr
open BudgetClock.NonMonotone BudgetClock.Monotone BCNMInv

variable {n : ℕ}

theorem phaseEnd_zero (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (B : ℝ) :
    phaseEnd v c B 0 = initState v B := rfl

theorem phaseEnd_succ (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (B : ℝ) (k : ℕ) :
    phaseEnd v c B (k + 1) = outerStep v c B (phaseEnd v c B k) := by
  unfold phaseEnd; rw [Function.iterate_succ_apply']

theorem innerStep_t (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (B : ℝ) (s : State n)
    (i : Fin n) : (innerStep v c B s i).t = s.t := by
  unfold innerStep; simp only; split_ifs <;> rfl

theorem innerStep_A (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (B : ℝ) (s : State n)
    (i : Fin n) : (innerStep v c B s i).A ⊆ s.A := by
  unfold innerStep; simp only; split_ifs
  all_goals first | exact Finset.Subset.refl _ | exact Finset.erase_subset _ _

theorem innerLoop_t (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (B : ℝ) :
    ∀ (k : ℕ) (s : State n), (innerLoop v c B k s).t = s.t := by
  intro k
  induction k with
  | zero => intro s; rfl
  | succ k ih =>
    intro s
    unfold innerLoop
    split_ifs
    · rfl
    · split
      · rfl
      · rw [ih, innerStep_t]

theorem innerLoop_A (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (B : ℝ) :
    ∀ (k : ℕ) (s : State n), (innerLoop v c B k s).A ⊆ s.A := by
  intro k
  induction k with
  | zero => intro s; exact le_rfl
  | succ k ih =>
    intro s
    unfold innerLoop
    split_ifs
    · exact le_rfl
    · split
      · exact le_rfl
      · exact (ih _).trans (innerStep_A _ _ _ _ _)

/-- The state at the start of a phase, after line 3. -/
def reset (s : State n) : State n :=
  State.mk s.A s.cur1 s.cur2 [] [] (2 * s.tgt) (s.t + 1) s.p

theorem phase_eq (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (B : ℝ) (s : State n) :
    phase v c B s = innerLoop v c B n (reset s) := rfl

theorem phase_t (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (B : ℝ) (s : State n) :
    (phase v c B s).t = s.t + 1 := by
  rw [phase_eq, innerLoop_t]; rfl

theorem phase_tgt (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (B : ℝ) (s : State n) :
    (phase v c B s).tgt = 2 * s.tgt := by
  rw [phase_eq, BCNMInv.innerLoop_tgt]; rfl

theorem phase_A (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (B : ℝ) (s : State n) :
    (phase v c B s).A ⊆ s.A := by
  rw [phase_eq]; exact innerLoop_A _ _ _ _ _

theorem outerStep_cases (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (B : ℝ) (s : State n) :
    ((pool s).Nonempty ∧ outerStep v c B s = phase v c B s) ∨
      (pool s = ∅ ∧ outerStep v c B s = s) := by
  unfold outerStep
  by_cases h : (pool s).Nonempty
  · left; exact ⟨h, by rw [if_pos h]⟩
  · right; exact ⟨Finset.not_nonempty_iff_eq_empty.1 h, by rw [if_neg h]⟩

theorem phaseEnd_A_succ (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (B : ℝ) (k : ℕ) :
    (phaseEnd v c B (k + 1)).A ⊆ (phaseEnd v c B k).A := by
  rw [phaseEnd_succ]
  rcases outerStep_cases v c B (phaseEnd v c B k) with ⟨_, h⟩ | ⟨_, h⟩
  · rw [h]; exact phase_A _ _ _ _
  · rw [h]

theorem phaseEnd_A_mono (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (B : ℝ) {j k : ℕ}
    (hjk : j ≤ k) : (phaseEnd v c B k).A ⊆ (phaseEnd v c B j).A := by
  induction k with
  | zero => rw [Nat.le_zero.1 hjk]
  | succ k ih =>
    rcases Nat.lt_or_ge j (k + 1) with h | h
    · exact (phaseEnd_A_succ v c B k).trans (ih (Nat.lt_succ_iff.1 h))
    · rw [le_antisymm hjk h]

theorem phaseEnd_t_succ (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (B : ℝ) (k : ℕ) :
    ((pool (phaseEnd v c B k)).Nonempty ∧
        phaseEnd v c B (k + 1) = phase v c B (phaseEnd v c B k) ∧
        (phaseEnd v c B (k + 1)).t = (phaseEnd v c B k).t + 1) ∨
      (pool (phaseEnd v c B k) = ∅ ∧ phaseEnd v c B (k + 1) = phaseEnd v c B k) := by
  rw [phaseEnd_succ]
  rcases outerStep_cases v c B (phaseEnd v c B k) with ⟨h1, h⟩ | ⟨h1, h⟩
  · left; exact ⟨h1, h, by rw [h, phase_t]⟩
  · right; exact ⟨h1, h⟩

theorem phaseEnd_stable (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (B : ℝ) {k : ℕ}
    (h : pool (phaseEnd v c B k) = ∅) : ∀ j, k ≤ j → phaseEnd v c B j = phaseEnd v c B k := by
  intro j hj
  induction j with
  | zero => rw [Nat.le_zero.1 hj]
  | succ j ih =>
    rcases Nat.lt_or_ge k (j + 1) with h' | h'
    · have e := ih (Nat.lt_succ_iff.1 h')
      rcases phaseEnd_t_succ v c B j with ⟨hn, _, _⟩ | ⟨_, h2⟩
      · rw [e, h] at hn; simp at hn
      · rw [h2, e]
    · rw [le_antisymm hj h']

theorem phaseEnd_t_le (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (B : ℝ) (k : ℕ) :
    1 ≤ (phaseEnd v c B k).t ∧ (phaseEnd v c B k).t ≤ k + 1 := by
  induction k with
  | zero => simp [phaseEnd_zero, initState]
  | succ k ih =>
    rcases phaseEnd_t_succ v c B k with ⟨_, _, h⟩ | ⟨_, h⟩
    · rw [h]; omega
    · rw [h]; omega

theorem phaseEnd_t_lt (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (B : ℝ) (k : ℕ) :
    (phaseEnd v c B k).t < k + 1 → pool (phaseEnd v c B k) = ∅ := by
  induction k with
  | zero => intro h; simp [phaseEnd_zero, initState] at h
  | succ k ih =>
    intro h
    rcases phaseEnd_t_succ v c B k with ⟨hn, he, ht⟩ | ⟨hp, he⟩
    · have : (phaseEnd v c B k).t < k + 1 := by omega
      rw [ih this] at hn; simp at hn
    · rw [he]; exact hp

theorem phaseEnd_t_of_le_last (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (B : ℝ) {t : ℕ}
    (ht1 : 1 ≤ t) (ht : t ≤ lastPhase v c B) : (phaseEnd v c B (t - 1)).t = t := by
  have hb := phaseEnd_t_le v c B (t - 1)
  by_contra hne
  have hlt : (phaseEnd v c B (t - 1)).t < t - 1 + 1 := by omega
  have hp := phaseEnd_t_lt v c B (t - 1) hlt
  unfold lastPhase finalState at ht
  rcases Nat.lt_or_ge (n + 2) (t - 1) with h | h
  · have := (phaseEnd_t_le v c B (n + 2)).2; omega
  · rw [phaseEnd_stable v c B hp (n + 2) h] at ht; omega

/-- `m = v(S²_1)`. -/
noncomputable def mval (v : Finset (Fin n) → ℝ) : ℝ := v (bestSingleton v).toFinset

theorem phaseEnd_tgt (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (B : ℝ) (k : ℕ) :
    (phaseEnd v c B k).tgt = target v (phaseEnd v c B k).t := by
  induction k with
  | zero => simp [phaseEnd_zero, initState, target]
  | succ k ih =>
    rcases phaseEnd_t_succ v c B k with ⟨_, he, ht⟩ | ⟨_, he⟩
    · rw [ht, he, phase_tgt, ih]
      obtain ⟨h1, _⟩ := phaseEnd_t_le v c B k
      obtain ⟨j, hj⟩ : ∃ j, (phaseEnd v c B k).t = j + 1 := ⟨_, (Nat.succ_pred_eq_of_pos h1).symm⟩
      rw [hj]; simp [target, pow_succ]; ring
    · rw [he, ih]

/-- For `2 ≤ t ≤ t̂`, phase `t` really runs: it maps the state after phase `t-1` to the state
after phase `t`. -/
theorem phase_runs (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (B : ℝ) {k : ℕ}
    (ht : k + 2 ≤ lastPhase v c B) :
    (pool (phaseEnd v c B k)).Nonempty ∧
      phaseEnd v c B (k + 1) = phase v c B (phaseEnd v c B k) := by
  have h1 := phaseEnd_t_of_le_last v c B (t := k + 2) (by omega) ht
  have h0 := phaseEnd_t_of_le_last v c B (t := k + 1) (by omega) (by omega)
  rw [show k + 2 - 1 = k + 1 by omega] at h1
  rw [show k + 1 - 1 = k by omega] at h0
  rcases phaseEnd_t_succ v c B k with ⟨hn, he, _⟩ | ⟨_, he⟩
  · exact ⟨hn, he⟩
  · rw [he] at h1; omega

/-! Facts about `v`. -/

theorem empty_le_two {v : Finset (Fin n) → ℝ} (hv : ∀ S, 0 ≤ v S)
    (hsub : NonmonotoneSubmod.Shared.Submodular v) (hn : 2 ≤ n) (M : ℝ)
    (hM : ∀ j, v {j} ≤ M) : v ∅ ≤ 2 * M := by
  have a : Fin n := ⟨0, by omega⟩
  let a : Fin n := ⟨0, by omega⟩
  let b : Fin n := ⟨1, by omega⟩
  have hab : a ≠ b := by simp [a, b, Fin.ext_iff]
  have h := submod_single hsub {a} (a := b) (by simpa using hab.symm)
  have := hv ({a} ∪ {b})
  linarith [hM a, hM b]

/-- Sum-of-marginals bound for submodular `v`. -/
theorem sum_marg {v : Finset (Fin n) → ℝ} (hsub : NonmonotoneSubmod.Shared.Submodular v)
    (S : Finset (Fin n)) : ∀ R : Finset (Fin n), Disjoint R S →
      v (S ∪ R) ≤ v S + ∑ r ∈ R, marg v {r} S := by
  intro R
  induction R using Finset.induction_on with
  | empty => intro _; simp
  | insert a R ha ih =>
    intro hd
    have hd' : Disjoint R S := Finset.disjoint_of_subset_left (Finset.subset_insert _ _) hd
    have haS : a ∉ S := Finset.disjoint_left.1 hd (Finset.mem_insert_self _ _)
    have h1 := ih hd'
    have h2 := submod_marg hsub (A := S) (C := S ∪ R) Finset.subset_union_left
      (i := a) (by simp [haS, ha])
    rw [Finset.sum_insert ha]
    have e : S ∪ insert a R = S ∪ R ∪ {a} := by
      ext x; simp
    rw [e]
    unfold marg
    unfold marg at h1
    linarith

/-! The rejection invariant inside a phase. -/

/-- Rejection invariant relative to the active set `A0` at the start of the phase and a set `O`
of bidders with `c i ≤ B`. -/
def RInv (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (B : ℝ) (A0 O : Finset (Fin n))
    (s : State n) : Prop :=
  s.A ⊆ A0 ∧
    (∀ i ∈ O, i ∈ A0 → i ∉ s.A → i ∉ s.cur1 ∧ i ∉ s.cur2 ∧
      marg v {i} s.cur1.toFinset * B < c i * s.tgt ∧
      marg v {i} s.cur2.toFinset * B < c i * s.tgt) ∧
    (∀ i ∈ s.A, c i ≤ B → c i ≤ s.p i)

theorem innerStep_rinv {v : Finset (Fin n) → ℝ} (hv : ∀ S, 0 ≤ v S)
    (hsub : NonmonotoneSubmod.Shared.Submodular v) {c : Fin n → ℝ} (hc : ∀ i, 0 ≤ c i)
    {B : ℝ} (hB : 0 < B) {A0 O : Finset (Fin n)} (hOB : ∀ i ∈ O, c i ≤ B)
    {s : State n} (hs : RInv v c B A0 O s) {i : Fin n} (hi : i ∈ pool s)
    (hlt : ¬ s.tgt ≤ max (v s.cur1.toFinset) (v s.cur2.toFinset)) :
    RInv v c B A0 O (innerStep v c B s i) := by
  obtain ⟨hA, hp1, hp2, hc1, hc2⟩ := mem_pool hi
  push Not at hlt
  have hτ : 0 < s.tgt := lt_of_le_of_lt (le_trans (hv _) (le_max_left _ _)) hlt
  obtain ⟨r1, r2, r3⟩ := hs
  unfold innerStep
  simp only
  set m1 := marg v {i} s.cur1.toFinset with hm1
  set m2 := marg v {i} s.cur2.toFinset with hm2
  set x := min (s.p i) ((if m2 ≤ m1 then m1 else m2) * B / s.tgt) with hx
  have grow : ∀ (L : List (Fin n)) (r : Fin n), r ∉ L → r ≠ i →
      marg v {r} (L ++ [i]).toFinset ≤ marg v {r} L.toFinset := by
    intro L r hr hri
    have e : (L ++ [i]).toFinset = L.toFinset ∪ {i} := by rw [List.toFinset_append]; simp
    rw [e]; unfold marg
    rw [Finset.union_comm _ {r}, Finset.union_comm _ {r}]
    have := submod_marg hsub (A := L.toFinset) (C := L.toFinset ∪ {i})
      Finset.subset_union_left (i := r) (by simp [hr, hri])
    rw [Finset.union_comm {r}, Finset.union_comm {r}]
    linarith
  split_ifs with hcx hm
  · refine ⟨r1, fun r hrO hr0 hrA => ?_, fun j hj hjB => ?_⟩
    · obtain ⟨a1, a2, a3, a4⟩ := r2 r hrO hr0 hrA
      have hri : r ≠ i := by rintro rfl; exact hrA hA
      refine ⟨by simp [a1, hri], a2, ?_, a4⟩
      have := grow s.cur1 r a1 hri
      nlinarith
    · by_cases hji : j = i
      · subst hji; simp; exact hcx
      · dsimp only; rw [Function.update_of_ne hji]; exact r3 j hj hjB
  · refine ⟨r1, fun r hrO hr0 hrA => ?_, fun j hj hjB => ?_⟩
    · obtain ⟨a1, a2, a3, a4⟩ := r2 r hrO hr0 hrA
      have hri : r ≠ i := by rintro rfl; exact hrA hA
      refine ⟨a1, by simp [a2, hri], a3, ?_⟩
      have := grow s.cur2 r a2 hri
      nlinarith
    · by_cases hji : j = i
      · subst hji; simp; exact hcx
      · dsimp only; rw [Function.update_of_ne hji]; exact r3 j hj hjB
  · refine ⟨(Finset.erase_subset _ _).trans r1, fun r hrO hr0 hrA => ?_, fun j hj hjB => ?_⟩
    · by_cases hri : r = i
      · subst hri
        refine ⟨hc1, hc2, ?_⟩
        push Not at hcx
        have hpi := r3 r hA (hOB r hrO)
        have hxe : x = (if m2 ≤ m1 then m1 else m2) * B / s.tgt := by
          rw [hx]; apply min_eq_right
          by_contra hh; push Not at hh
          rw [hx, min_eq_left hh.le] at hcx; linarith
        have hk : (if m2 ≤ m1 then m1 else m2) * B < c r * s.tgt := by
          rw [hxe, div_lt_iff₀ hτ] at hcx; exact hcx
        have hk1 : m1 ≤ (if m2 ≤ m1 then m1 else m2) := by
          split_ifs with h <;> [exact le_rfl; exact (not_le.1 h).le]
        have hk2 : m2 ≤ (if m2 ≤ m1 then m1 else m2) := by
          split_ifs with h <;> [exact h; exact le_rfl]
        constructor <;> nlinarith
      · have hrA' : r ∉ s.A := by
          intro h; exact hrA (Finset.mem_erase.2 ⟨hri, h⟩)
        exact r2 r hrO hr0 hrA'
    · have hji : j ≠ i := (Finset.mem_erase.1 hj).1
      dsimp only; rw [Function.update_of_ne hji]; exact r3 j (Finset.mem_erase.1 hj).2 hjB

theorem innerLoop_rinv {v : Finset (Fin n) → ℝ} (hv : ∀ S, 0 ≤ v S)
    (hsub : NonmonotoneSubmod.Shared.Submodular v) {c : Fin n → ℝ} (hc : ∀ i, 0 ≤ c i)
    {B : ℝ} (hB : 0 < B) {A0 O : Finset (Fin n)} (hOB : ∀ i ∈ O, c i ≤ B) :
    ∀ (k : ℕ) (s : State n), RInv v c B A0 O s → RInv v c B A0 O (innerLoop v c B k s) := by
  intro k
  induction k with
  | zero => intro s hs; exact hs
  | succ k ih =>
    intro s hs
    unfold innerLoop
    split_ifs with h
    · exact hs
    · split
      · exact hs
      · rename_i i hi
        exact ih _ (innerStep_rinv hv hsub hc hB hOB hs (pickBidder_mem hi) h)

theorem reset_rinv {v : Finset (Fin n) → ℝ} {c : Fin n → ℝ} {B : ℝ} {O : Finset (Fin n)}
    {s : State n} (hP : ∀ i ∈ s.A, c i ≤ B → c i ≤ s.p i) :
    RInv v c B s.A O (reset s) :=
  ⟨le_rfl, fun _ _ h0 hA => absurd h0 hA, hP⟩

/-- Prices of active bidders with `c i ≤ B` stay at least their cost. -/
theorem phaseEnd_price {v : Finset (Fin n) → ℝ} (hv : ∀ S, 0 ≤ v S)
    (hsub : NonmonotoneSubmod.Shared.Submodular v) {c : Fin n → ℝ} (hc : ∀ i, 0 ≤ c i)
    {B : ℝ} (hB : 0 < B) (k : ℕ) :
    ∀ i ∈ (phaseEnd v c B k).A, c i ≤ B → c i ≤ (phaseEnd v c B k).p i := by
  induction k with
  | zero => intro i _ h; simpa [phaseEnd_zero, initState] using h
  | succ k ih =>
    rcases phaseEnd_t_succ v c B k with ⟨_, he, _⟩ | ⟨_, he⟩
    · rw [he, phase_eq]
      exact (innerLoop_rinv hv hsub hc hB (O := ∅) (by simp) n _ (reset_rinv ih)).2.2
    · rw [he]; exact ih

end BCNMTr

namespace BCNML7
open BudgetClock.NonMonotone BudgetClock.Monotone BCNMInv BCNMTr

variable {n : ℕ}

theorem mem_bestSingleton_of_le_one (v : Finset (Fin n) → ℝ) (hn : n ≤ 1) (i : Fin n) :
    i ∈ bestSingleton v := by
  unfold bestSingleton
  simp only
  split_ifs with hM
  · simp only [List.mem_singleton]
    apply Fin.ext; have := i.2; have := (Finset.min' _ hM).2; omega
  · exfalso
    obtain ⟨x, _, hx⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin n))
      (fun j => v {j}) ⟨i, Finset.mem_univ _⟩
    exact hM ⟨x, Finset.mem_filter.2 ⟨Finset.mem_univ _, fun j' => hx j' (Finset.mem_univ _)⟩⟩

theorem two_le_n_of_pool (v : Finset (Fin n) → ℝ) (B : ℝ)
    (h : (pool (initState v B)).Nonempty) : 2 ≤ n := by
  by_contra hn; push Not at hn
  obtain ⟨i, hi⟩ := h
  obtain ⟨_, _, _, _, h4⟩ := mem_pool hi
  exact h4 (mem_bestSingleton_of_le_one v (by omega) i)

theorem subadd {v : Finset (Fin n) → ℝ} (hv : ∀ S, 0 ≤ v S)
    (hsub : NonmonotoneSubmod.Shared.Submodular v) (X Y : Finset (Fin n)) :
    v (X ∪ Y) ≤ v X + v Y := by
  have := hsub X Y; have := hv (X ∩ Y); linarith

/-! Termination of the inner loop. -/

theorem innerStep_pool (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (B : ℝ) (s : State n)
    {i : Fin n} (hi : i ∈ pool s) : pool (innerStep v c B s i) ⊆ (pool s).erase i := by
  intro j hj
  unfold innerStep at hj
  simp only at hj
  unfold pool at hj ⊢
  split_ifs at hj <;>
  · simp only [Finset.mem_sdiff, Finset.mem_union, List.mem_toFinset, List.mem_append,
      List.mem_singleton, Finset.mem_erase, not_or] at hj ⊢
    tauto

theorem pickBidder_some {v : Finset (Fin n) → ℝ} {s : State n} (h : (pool s).Nonempty) :
    ∃ i, pickBidder v s = some i := by
  unfold pickBidder
  simp only
  obtain ⟨x, hx, hmax⟩ := Finset.exists_max_image (pool s) (bestMarg v s) h
  have hM : ((pool s).filter (fun i => ∀ j ∈ pool s, bestMarg v s j ≤ bestMarg v s i)).Nonempty :=
    ⟨x, Finset.mem_filter.2 ⟨hx, hmax⟩⟩
  rw [dif_pos hM]
  exact ⟨_, rfl⟩

theorem innerLoop_end (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (B : ℝ) :
    ∀ (k : ℕ) (s : State n), (pool s).card ≤ k →
      pool (innerLoop v c B k s) = ∅ ∨
        (innerLoop v c B k s).tgt ≤
          max (v (innerLoop v c B k s).cur1.toFinset) (v (innerLoop v c B k s).cur2.toFinset) := by
  intro k
  induction k with
  | zero =>
    intro s hs
    left; exact Finset.card_eq_zero.1 (Nat.le_zero.1 hs)
  | succ k ih =>
    intro s hs
    unfold innerLoop
    split_ifs with h
    · right; exact h
    · split
      · rename_i hnone
        left
        by_contra hne
        obtain ⟨i, hi⟩ := pickBidder_some (v := v) (Finset.nonempty_iff_ne_empty.2 hne)
        rw [hi] at hnone; cases hnone
      · rename_i i hi
        apply ih
        have hip := pickBidder_mem hi
        have h1 := Finset.card_le_card (innerStep_pool v c B s hip)
        rw [Finset.card_erase_of_mem hip] at h1
        omega

theorem phase_end (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (B : ℝ) (s : State n) :
    pool (phase v c B s) = ∅ ∨
      (phase v c B s).tgt ≤ max (v (phase v c B s).cur1.toFinset) (v (phase v c B s).cur2.toFinset) := by
  rw [phase_eq]
  apply innerLoop_end
  have := Finset.card_le_univ (pool (reset s))
  simpa using this

theorem innerStep_prev (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (B : ℝ) (s : State n)
    (i : Fin n) : (innerStep v c B s i).prev1 = s.prev1 ∧ (innerStep v c B s i).prev2 = s.prev2 := by
  unfold innerStep; simp only; split_ifs <;> exact ⟨rfl, rfl⟩

theorem innerLoop_prev (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (B : ℝ) :
    ∀ (k : ℕ) (s : State n), (innerLoop v c B k s).prev1 = s.prev1 ∧
      (innerLoop v c B k s).prev2 = s.prev2 := by
  intro k
  induction k with
  | zero => intro s; exact ⟨rfl, rfl⟩
  | succ k ih =>
    intro s
    unfold innerLoop
    split_ifs
    · exact ⟨rfl, rfl⟩
    · split
      · exact ⟨rfl, rfl⟩
      · rename_i i _
        obtain ⟨a, b⟩ := ih (innerStep v c B s i)
        obtain ⟨a', b'⟩ := innerStep_prev v c B s i
        exact ⟨a.trans a', b.trans b'⟩

theorem phase_prev (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (B : ℝ) (s : State n) :
    (phase v c B s).prev1 = s.cur1 ∧ (phase v c B s).prev2 = s.cur2 := by
  rw [phase_eq]; exact innerLoop_prev v c B n (reset s)

/-! The outer loop. -/

theorem phaseEnd_t_mono (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (B : ℝ) {j k : ℕ}
    (hjk : j ≤ k) : (phaseEnd v c B j).t ≤ (phaseEnd v c B k).t := by
  induction k with
  | zero => rw [Nat.le_zero.1 hjk]
  | succ k ih =>
    rcases Nat.lt_or_ge j (k + 1) with h | h
    · have := ih (Nat.lt_succ_iff.1 h)
      rcases phaseEnd_t_succ v c B k with ⟨_, _, h2⟩ | ⟨_, h2⟩
      · rw [h2]; omega
      · rw [h2]; exact this
    · rw [le_antisymm hjk h]

theorem phaseEnd_eq_of_t (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (B : ℝ) {j k : ℕ}
    (hjk : j ≤ k) (ht : (phaseEnd v c B j).t = (phaseEnd v c B k).t) :
    phaseEnd v c B k = phaseEnd v c B j := by
  rcases phaseEnd_t_succ v c B j with ⟨_, _, h2⟩ | ⟨hp, _⟩
  · rcases Nat.lt_or_ge j k with h | h
    · have := phaseEnd_t_mono v c B (j := j + 1) (k := k) h
      omega
    · rw [le_antisymm hjk h]
  · exact phaseEnd_stable v c B hp k hjk

theorem final_eq (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (B : ℝ) :
    finalState v c B = phaseEnd v c B (lastPhase v c B - 1) := by
  have h1 := (phaseEnd_t_le v c B (n + 2))
  have hl : lastPhase v c B = (phaseEnd v c B (n + 2)).t := rfl
  have h2 := phaseEnd_t_of_le_last v c B (t := lastPhase v c B) (by omega) le_rfl
  unfold finalState
  apply phaseEnd_eq_of_t v c B (by omega)
  rw [h2, hl]

/-- Value bound `v(S) ≤ v(∅) + |S| m` (singletons worth at most `m`). -/
theorem val_le_card {v : Finset (Fin n) → ℝ} (hv : ∀ S, 0 ≤ v S)
    (hsub : NonmonotoneSubmod.Shared.Submodular v) (m : ℝ) (hm : ∀ j, v {j} ≤ m)
    (S : Finset (Fin n)) : v S ≤ v ∅ + S.card * m := by
  have h := sum_marg hsub ∅ S (Finset.disjoint_empty_right _)
  simp only [Finset.empty_union, marg] at h
  have h2 : ∑ r ∈ S, (v {r} - v ∅) ≤ ∑ r ∈ S, m :=
    Finset.sum_le_sum (fun r _ => by linarith [hm r, hv ∅])
  rw [Finset.sum_const, nsmul_eq_mul] at h2
  linarith

theorem two_pow_gt (n : ℕ) (hn : 1 ≤ n) : (n : ℝ) + 2 < 2 ^ (n + 1) := by
  have h : n + 2 < 2 ^ (n + 1) := by
    have := Nat.lt_two_pow_self (n := n)
    rw [pow_succ]; omega
  exact_mod_cast h

/-- If the run is cut by the fuel, then `m = 0`. -/
theorem m_zero_of_running {v : Finset (Fin n) → ℝ} (hv : ∀ S, 0 ≤ v S)
    (hsub : NonmonotoneSubmod.Shared.Submodular v) {c : Fin n → ℝ} (hc : ∀ i, 0 ≤ c i)
    {B : ℝ} (hB : 0 < B) (h : (pool (finalState v c B)).Nonempty) :
    2 ≤ n ∧ v (bestSingleton v).toFinset = 0 := by
  have hall : ∀ k, k ≤ n + 2 → (pool (phaseEnd v c B k)).Nonempty := by
    intro k hk
    by_contra hne
    have he := phaseEnd_stable v c B (Finset.not_nonempty_iff_eq_empty.1 hne) (n + 2) hk
    unfold finalState at h; rw [he] at h; exact hne h
  have hn := two_le_n_of_pool v B (hall 0 (by omega))
  refine ⟨hn, ?_⟩
  -- phase `n + 2` reached its target
  have ht : ∀ k, k ≤ n + 2 → (phaseEnd v c B k).t = k + 1 := by
    intro k hk
    have := phaseEnd_t_le v c B k
    by_contra hne
    have hp := phaseEnd_t_lt v c B k (by omega)
    have := hall k hk; rw [hp] at this; simp at this
  have hs : phaseEnd v c B (n + 1) = phase v c B (phaseEnd v c B n) := by
    rcases phaseEnd_t_succ v c B n with ⟨_, he, _⟩ | ⟨hp, _⟩
    · exact he
    · have := hall n (by omega); rw [hp] at this; simp at this
  have hend := phase_end v c B (phaseEnd v c B n)
  rw [← hs] at hend
  have hreach : (phaseEnd v c B (n + 1)).tgt ≤
      max (v (phaseEnd v c B (n + 1)).cur1.toFinset) (v (phaseEnd v c B (n + 1)).cur2.toFinset) := by
    rcases hend with hp | hr
    · have := hall (n + 1) (by omega); rw [hp] at this; simp at this
    · exact hr
  rw [phaseEnd_tgt, ht (n + 1) (by omega)] at hreach
  simp only [target] at hreach
  set m := v (bestSingleton v).toFinset
  have hm := (bestSingleton_spec v).2
  have he := empty_le_two hv hsub hn m hm
  have hcard : ∀ S : Finset (Fin n), v S ≤ (n + 2) * m := by
    intro S
    have h1 := val_le_card hv hsub m hm S
    have h2 : (S.card : ℝ) ≤ n := by
      have := Finset.card_le_univ S; simp at this; exact_mod_cast this
    have hm0 : 0 ≤ m := hv _
    nlinarith
  have hmax : max (v (phaseEnd v c B (n + 1)).cur1.toFinset)
      (v (phaseEnd v c B (n + 1)).cur2.toFinset) ≤ (n + 2) * m :=
    max_le (hcard _) (hcard _)
  have hpow := two_pow_gt n (by omega)
  have hm0 : 0 ≤ m := hv _
  by_contra hm1
  have hmpos : 0 < m := lt_of_le_of_ne hm0 (Ne.symm hm1)
  nlinarith

theorem usmList_toFinset (usm : Finset (Fin n) → Finset (Fin n))
    (husm : ∀ X, usm X ⊆ X) (L : List (Fin n)) :
    (usmList usm L).toFinset = usm L.toFinset := by
  unfold usmList
  ext x
  simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨_, h⟩; exact h
  · intro h; exact ⟨List.mem_toFinset.1 (husm _ h), h⟩

theorem lemma7 (v : Finset (Fin n) → ℝ) (hv : ∀ S, 0 ≤ v S)
    (hsub : NonmonotoneSubmod.Shared.Submodular v)
    (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i) (B : ℝ) (hB : 0 < B)
    (usm : Finset (Fin n) → Finset (Fin n))
    (husm : ∀ X, usm X ⊆ X ∧ ∀ Y ⊆ X, v Y ≤ 2 * v (usm X))
    (O : Finset (Fin n)) (hO : ∑ i ∈ O, c i ≤ B) :
    ∃ L ∈ candidates usm (finalState v c B), v O / 32 ≤ v L.toFinset := by
  set s := finalState v c B with hsdef
  have hvO := hv O
  by_cases hrun : (pool s).Nonempty
  · -- the fuel ran out: then `v ≡ 0`
    obtain ⟨hn, hm⟩ := m_zero_of_running hv hsub hc hB hrun
    have hmj := (bestSingleton_spec v).2
    have he := empty_le_two hv hsub hn _ hmj
    have h1 := val_le_card hv hsub _ hmj O
    rw [hm] at he h1
    refine ⟨s.prev1, by simp [candidates], ?_⟩
    have := hv s.prev1.toFinset
    linarith
  rw [Finset.not_nonempty_iff_eq_empty] at hrun
  -- the active bidders are covered by the four tentative sets
  set T1 := usmList usm s.cur1
  set T2 := usmList usm s.cur2
  set T3 := usmList usm s.prev1
  set T4 := usmList usm s.prev2
  have hcover : s.A ⊆ s.prev1.toFinset ∪ s.prev2.toFinset ∪ s.cur1.toFinset ∪ s.cur2.toFinset := by
    intro x hx
    by_contra hh
    have : x ∈ pool s := by unfold pool; exact Finset.mem_sdiff.2 ⟨hx, hh⟩
    rw [hrun] at this; simp at this
  have hT : ∀ L : List (Fin n), v (O ∩ s.A ∩ L.toFinset) ≤ 2 * v (usmList usm L).toFinset := by
    intro L
    rw [usmList_toFinset usm (fun X => (husm X).1)]
    exact (husm _).2 _ Finset.inter_subset_right
  have hsplit : O ∩ s.A = (O ∩ s.A ∩ s.prev1.toFinset) ∪ (O ∩ s.A ∩ s.prev2.toFinset) ∪
      (O ∩ s.A ∩ s.cur1.toFinset) ∪ (O ∩ s.A ∩ s.cur2.toFinset) := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_union]
    constructor
    · rintro ⟨h1, h2⟩
      have := hcover h2
      simp only [Finset.mem_union] at this
      tauto
    · tauto
  have hplus : v (O ∩ s.A) ≤ 8 * max (max (v T1.toFinset) (v T2.toFinset))
      (max (v T3.toFinset) (v T4.toFinset)) := by
    rw [hsplit]
    have a1 := subadd hv hsub ((O ∩ s.A ∩ s.prev1.toFinset) ∪ (O ∩ s.A ∩ s.prev2.toFinset) ∪
      (O ∩ s.A ∩ s.cur1.toFinset)) (O ∩ s.A ∩ s.cur2.toFinset)
    have a2 := subadd hv hsub ((O ∩ s.A ∩ s.prev1.toFinset) ∪ (O ∩ s.A ∩ s.prev2.toFinset))
      (O ∩ s.A ∩ s.cur1.toFinset)
    have a3 := subadd hv hsub (O ∩ s.A ∩ s.prev1.toFinset) (O ∩ s.A ∩ s.prev2.toFinset)
    have b1 := hT s.cur1
    have b2 := hT s.cur2
    have b3 := hT s.prev1
    have b4 := hT s.prev2
    have c1 := le_max_left (v T1.toFinset) (v T2.toFinset)
    have c2 := le_max_right (v T1.toFinset) (v T2.toFinset)
    have c3 := le_max_left (v T3.toFinset) (v T4.toFinset)
    have c4 := le_max_right (v T3.toFinset) (v T4.toFinset)
    have d1 := le_max_left (max (v T1.toFinset) (v T2.toFinset)) (max (v T3.toFinset) (v T4.toFinset))
    have d2 := le_max_right (max (v T1.toFinset) (v T2.toFinset)) (max (v T3.toFinset) (v T4.toFinset))
    linarith
  -- a candidate of value at least the max of the T's
  have hTmem : ∃ L ∈ candidates usm s, max (max (v T1.toFinset) (v T2.toFinset))
      (max (v T3.toFinset) (v T4.toFinset)) ≤ v L.toFinset := by
    rcases le_total (max (v T1.toFinset) (v T2.toFinset)) (max (v T3.toFinset) (v T4.toFinset))
      with h | h
    · rw [max_eq_right h]
      rcases le_total (v T3.toFinset) (v T4.toFinset) with h' | h'
      · exact ⟨T4, by simp [candidates, T4], by rw [max_eq_right h']⟩
      · exact ⟨T3, by simp [candidates, T3], by rw [max_eq_left h']⟩
    · rw [max_eq_left h]
      rcases le_total (v T1.toFinset) (v T2.toFinset) with h' | h'
      · exact ⟨T2, by simp [candidates, T2], by rw [max_eq_right h']⟩
      · exact ⟨T1, by simp [candidates, T1], by rw [max_eq_left h']⟩
  obtain ⟨LT, hLT, hLTv⟩ := hTmem
  -- phase bookkeeping
  set th := lastPhase v c B with hth
  have hfe := final_eq v c B
  rw [← hsdef, ← hth] at hfe
  have hth1 : 1 ≤ th := (phaseEnd_t_le v c B (n + 2)).1
  have hsurv : survivors v c B th = s.A := by
    obtain ⟨k, hk⟩ : ∃ k, th = k + 1 := ⟨th - 1, by omega⟩
    rw [hk]; show (phaseEnd v c B k).A = s.A
    rw [hfe, hk]; rfl
  have hc1 := corollary_1 v hv hsub c hc B hB O hO th hth1 le_rfl
  rw [hsurv] at hc1
  have htgt : target v th = s.tgt := by
    rw [hsdef]; unfold finalState; rw [phaseEnd_tgt]; rfl
  rw [htgt] at hc1
  by_cases hcase : 16 * s.tgt < v O
  · exact ⟨LT, hLT, by linarith⟩
  · push Not at hcase
    -- the previous phase reached its target `s.tgt / 2`
    have hprev : ∃ L ∈ candidates usm s, s.tgt / 2 ≤ v L.toFinset ∨ v O ≤ 8 * v L.toFinset := by
      obtain ⟨k, hk⟩ : ∃ k, th = k + 1 := ⟨th - 1, by omega⟩
      rcases k with _ | k
      · -- `t̂ = 1`: every bidder of `O` is still active
        refine ⟨LT, hLT, Or.inr ?_⟩
        have hA : s.A = Finset.univ := by
          rw [← hsurv, hk]; simp [survivors, phaseEnd_zero, initState]
        rw [hA, Finset.inter_univ] at hplus
        linarith
      · rcases k with _ | k
        · -- `t̂ = 2`: `S²_1` is the best singleton
          have hr := phase_runs v c B (k := 0) (by omega)
          have hsk : s = phaseEnd v c B 1 := by rw [hfe, hk]
          refine ⟨s.prev2, by simp [candidates], Or.inl ?_⟩
          have hp2 : s.prev2 = bestSingleton v := by
            rw [hsk, hr.2, (phase_prev v c B _).2, phaseEnd_zero]; rfl
          have hst : s.tgt = 2 * v (bestSingleton v).toFinset := by
            rw [hsk, hr.2, phase_tgt, phaseEnd_zero]; rfl
          rw [hp2, hst]; linarith
        · -- `t̂ ≥ 3`: phase `t̂ - 1 ≥ 2` ended with a nonempty pool
          have hr1 := phase_runs v c B (k := k + 1) (by omega)
          have hr0 := phase_runs v c B (k := k) (by omega)
          have hsk : s = phaseEnd v c B (k + 2) := by rw [hfe, hk]; rfl
          have hp := phase_prev v c B (phaseEnd v c B (k + 1))
          have hst : s.tgt = 2 * (phaseEnd v c B (k + 1)).tgt := by
            rw [hsk, hr1.2, phase_tgt]
          have hend := phase_end v c B (phaseEnd v c B k)
          rw [← hr0.2] at hend
          have hreach : (phaseEnd v c B (k + 1)).tgt ≤
              max (v (phaseEnd v c B (k + 1)).cur1.toFinset)
                (v (phaseEnd v c B (k + 1)).cur2.toFinset) := by
            rcases hend with h0 | h0
            · have := hr1.1; rw [h0] at this; simp at this
            · exact h0
          have e1 : s.prev1 = (phaseEnd v c B (k + 1)).cur1 := by rw [hsk, hr1.2, hp.1]
          have e2 : s.prev2 = (phaseEnd v c B (k + 1)).cur2 := by rw [hsk, hr1.2, hp.2]
          rcases le_total (v (phaseEnd v c B (k + 1)).cur1.toFinset)
              (v (phaseEnd v c B (k + 1)).cur2.toFinset) with h | h
          · refine ⟨s.prev2, by simp [candidates], Or.inl ?_⟩
            rw [max_eq_right h] at hreach; rw [e2, hst]; linarith
          · refine ⟨s.prev1, by simp [candidates], Or.inl ?_⟩
            rw [max_eq_left h] at hreach; rw [e1, hst]; linarith
    obtain ⟨L, hL, hLv⟩ := hprev
    refine ⟨L, hL, ?_⟩
    have := hv L.toFinset
    rcases hLv with h | h <;> linarith

end BCNML7

open BudgetClock.NonMonotone

theorem solution {n : ℕ} (v : Finset (Fin n) → ℝ) (hv : ∀ S, 0 ≤ v S)
    (hsub : NonmonotoneSubmod.Shared.Submodular v)
    (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i) (B : ℝ) (hB : 0 < B)
    (usm : Finset (Fin n) → Finset (Fin n))
    (husm : ∀ X, usm X ⊆ X ∧ ∀ Y ⊆ X, v Y ≤ 2 * v (usm X))
    (O : Finset (Fin n)) (hO : ∑ i ∈ O, c i ≤ B) :
    ∃ L ∈ candidates usm (finalState v c B), v O / 32 ≤ v L.toFinset :=
  BCNML7.lemma7 v hv hsub c hc B hB usm husm O hO
