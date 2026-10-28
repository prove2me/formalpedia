-- Prove2me | solution 1 for BudgetClock.Monotone.lemma_9
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T08:53:12.912076+00:00
-- url     : https://prove2.me/submissions/b7c3682b-8ba5-430c-bb3a-1bd23b344689

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_BudgetClock_Monotone_Mechanism
namespace BCMCore
open BudgetClock.Monotone

variable {n : ℕ}

/-! ## General facts about set functions -/

theorem marg_anti {v : Finset (Fin n) → ℝ} (hmono : IsMonotone v)
    (hsub : NonmonotoneSubmod.Shared.Submodular v) {S T : Finset (Fin n)} (X : Finset (Fin n))
    (h : S ⊆ T) : marg v X T ≤ marg v X S := by
  unfold marg
  have h1 := hsub (S ∪ X) T
  have e1 : S ∪ X ∪ T = T ∪ X := by
    ext x; simp only [Finset.mem_union]; constructor
    · rintro ((hx | hx) | hx)
      · exact Or.inl (h hx)
      · exact Or.inr hx
      · exact Or.inl hx
    · rintro (hx | hx)
      · exact Or.inr hx
      · exact Or.inl (Or.inr hx)
  have h2 : S ⊆ (S ∪ X) ∩ T := by
    intro x hx; exact Finset.mem_inter.2 ⟨Finset.mem_union_left _ hx, h hx⟩
  have h3 := hmono _ _ h2
  rw [e1] at h1
  have e2 : S ∪ X = S ∪ X := rfl
  linarith

theorem marg_nonneg {v : Finset (Fin n) → ℝ} (hmono : IsMonotone v) (X S : Finset (Fin n)) :
    0 ≤ marg v X S := by
  unfold marg
  have := hmono S (S ∪ X) Finset.subset_union_left
  linarith

theorem marg_le_sum {v : Finset (Fin n) → ℝ} (hmono : IsMonotone v)
    (hsub : NonmonotoneSubmod.Shared.Submodular v) (X : Finset (Fin n)) :
    ∀ Q : Finset (Fin n), marg v Q X ≤ ∑ j ∈ Q, marg v {j} X := by
  intro Q
  induction Q using Finset.induction_on with
  | empty => simp [marg]
  | insert a Q ha ih =>
    rw [Finset.sum_insert ha]
    have h1 := marg_anti hmono hsub {a} (Finset.subset_union_left : X ⊆ X ∪ Q)
    unfold marg at h1 ih ⊢
    have e : X ∪ insert a Q = X ∪ Q ∪ {a} := by
      ext x; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]; tauto
    rw [e]
    linarith

theorem marg_union_le {v : Finset (Fin n) → ℝ} (hmono : IsMonotone v)
    (hsub : NonmonotoneSubmod.Shared.Submodular v) (X Q1 Q2 : Finset (Fin n)) :
    marg v (Q1 ∪ Q2) X ≤ marg v Q1 X + marg v Q2 X := by
  have h1 := marg_anti hmono hsub Q2 (Finset.subset_union_left : X ⊆ X ∪ Q1)
  unfold marg at h1 ⊢
  have e : X ∪ (Q1 ∪ Q2) = X ∪ Q1 ∪ Q2 := by rw [Finset.union_assoc]
  rw [e]
  linarith

theorem subadd {v : Finset (Fin n) → ℝ} (hv : ∀ S, 0 ≤ v S)
    (hsub : NonmonotoneSubmod.Shared.Submodular v) (S T : Finset (Fin n)) :
    v (S ∪ T) ≤ v S + v T := by
  have := hsub S T
  have := hv (S ∩ T)
  linarith

theorem marg_le_val {v : Finset (Fin n) → ℝ} (hv : ∀ S, 0 ≤ v S)
    (hsub : NonmonotoneSubmod.Shared.Submodular v) (Q X : Finset (Fin n)) :
    marg v Q X ≤ v Q := by
  unfold marg
  have := subadd hv hsub X Q
  linarith

theorem subadd_biUnion {v : Finset (Fin n) → ℝ} (hv : ∀ S, 0 ≤ v S)
    (hsub : NonmonotoneSubmod.Shared.Submodular v) {ι : Type} [DecidableEq ι]
    (I : Finset ι) (f : ι → Finset (Fin n)) :
    v (I.biUnion f) ≤ v ∅ + ∑ k ∈ I, v (f k) := by
  induction I using Finset.induction_on with
  | empty => simp
  | insert a I ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    have := subadd hv hsub (f a) (I.biUnion f)
    linarith

theorem val_le_card {v : Finset (Fin n) → ℝ} (hv : ∀ S, 0 ≤ v S)
    (hsub : NonmonotoneSubmod.Shared.Submodular v) (m : ℝ) (hm : ∀ j, v {j} ≤ m) :
    ∀ S : Finset (Fin n), S.Nonempty → v S ≤ S.card * m := by
  intro S
  induction S using Finset.induction_on with
  | empty => intro h; simp at h
  | insert a S ha ih =>
    intro _
    rw [Finset.card_insert_of_notMem ha]
    by_cases hS : S.Nonempty
    · have h1 := ih hS
      have h2 := subadd hv hsub {a} S
      rw [Finset.insert_eq]
      push_cast
      linarith [hm a]
    · rw [Finset.not_nonempty_iff_eq_empty] at hS
      subst hS
      simp [hm a]

theorem marg_single_le {v : Finset (Fin n) → ℝ} (hv : ∀ S, 0 ≤ v S)
    (hsub : NonmonotoneSubmod.Shared.Submodular v) (m : ℝ) (hm : ∀ j, v {j} ≤ m)
    (j : Fin n) (X : Finset (Fin n)) : marg v {j} X ≤ m :=
  (marg_le_val hv hsub {j} X).trans (hm j)

/-! ## Lists -/

theorem listCost_append_single (p : Fin n → ℝ) (T : List (Fin n)) (i : Fin n) :
    listCost p (T ++ [i]) = listCost p T + p i := by
  simp [listCost]

theorem listCost_nil (p : Fin n → ℝ) : listCost p ([] : List (Fin n)) = 0 := by
  simp [listCost]

theorem listCost_congr {p p' : Fin n → ℝ} {T : List (Fin n)}
    (h : ∀ i ∈ T, p' i = p i) : listCost p' T = listCost p T := by
  unfold listCost
  rw [List.map_congr_left h]

theorem listCost_sublist_le {p : Fin n → ℝ} {T L : List (Fin n)} (h : T.Sublist L)
    (hp : ∀ i ∈ L, 0 ≤ p i) : listCost p T ≤ listCost p L := by
  unfold listCost
  apply (h.map p).sum_le_sum
  intro a ha
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 ha
  exact hp i hi

theorem listCost_nonneg {p : Fin n → ℝ} {L : List (Fin n)} (hp : ∀ i ∈ L, 0 ≤ p i) :
    0 ≤ listCost p L := by
  have := listCost_sublist_le (List.nil_sublist L) hp
  rwa [listCost_nil] at this

theorem sum_toFinset_le {p : Fin n → ℝ} (L : List (Fin n)) (hp : ∀ i ∈ L, 0 ≤ p i) :
    ∑ i ∈ L.toFinset, p i ≤ listCost p L := by
  have e : L.toFinset = L.dedup.toFinset := by ext; simp
  rw [e, List.sum_toFinset _ (List.nodup_dedup L)]
  exact listCost_sublist_le (List.dedup_sublist L) hp

theorem take_toFinset_sub (L : List (Fin n)) (k : ℕ) : (L.take k).toFinset ⊆ L.toFinset := by
  intro x hx
  simp only [List.mem_toFinset] at hx ⊢
  exact List.mem_of_mem_take hx

/-- Telescoping along a list: if each element's price times `τ` is at most `B` times its marginal
contribution when added, the cost times `τ` is at most `B (v L − v ∅)`. -/
theorem cost_le_of_marg {v : Finset (Fin n) → ℝ} {p : Fin n → ℝ} {τ B : ℝ} (L : List (Fin n))
    (h : ∀ k (hk : k < L.length), p L[k] * τ ≤ B * marg v {L[k]} (L.take k).toFinset) :
    listCost p L * τ ≤ B * (v L.toFinset - v ∅) := by
  have key : ∀ k, k ≤ L.length → listCost p (L.take k) * τ ≤
      B * (v (L.take k).toFinset - v ∅) := by
    intro k
    induction k with
    | zero => intro _; simp [listCost]
    | succ k ih =>
      intro hk
      have hk' : k < L.length := by omega
      rw [List.take_succ_eq_append_getElem hk', listCost_append_single]
      have e : (L.take k ++ [L[k]]).toFinset = (L.take k).toFinset ∪ {L[k]} := by
        simp only [List.toFinset_append, List.toFinset_cons, List.toFinset_nil, insert_empty_eq]
      rw [e]
      have h1 := ih (by omega)
      have h2 := h k hk'
      unfold marg at h2
      nlinarith
  have := key L.length le_rfl
  rwa [List.take_length] at this

theorem cost_ge_of_marg {v : Finset (Fin n) → ℝ} {p : Fin n → ℝ} {τ B : ℝ} (L : List (Fin n))
    (h : ∀ k (hk : k < L.length), B * marg v {L[k]} (L.take k).toFinset ≤ p L[k] * τ) :
    B * (v L.toFinset - v ∅) ≤ listCost p L * τ := by
  have key : ∀ k, k ≤ L.length → B * (v (L.take k).toFinset - v ∅) ≤
      listCost p (L.take k) * τ := by
    intro k
    induction k with
    | zero => intro _; simp [listCost]
    | succ k ih =>
      intro hk
      have hk' : k < L.length := by omega
      rw [List.take_succ_eq_append_getElem hk', listCost_append_single]
      have e : (L.take k ++ [L[k]]).toFinset = (L.take k).toFinset ∪ {L[k]} := by
        simp only [List.toFinset_append, List.toFinset_cons, List.toFinset_nil, insert_empty_eq]
      rw [e]
      have h1 := ih (by omega)
      have h2 := h k hk'
      unfold marg at h2
      nlinarith
  have := key L.length le_rfl
  rwa [List.take_length] at this

end BCMCore

namespace BCMCore
open BudgetClock.Monotone

variable {n : ℕ}

/-! ## The mechanism: one inner step -/

theorem pickBidder_some {v : Finset (Fin n) → ℝ} {s : State n} {i : Fin n}
    (h : pickBidder v s = some i) :
    i ∈ pool s ∧ ∀ j ∈ pool s, marg v {j} s.cur.toFinset ≤ marg v {i} s.cur.toFinset := by
  unfold pickBidder at h
  simp only at h
  split_ifs at h with hM
  · simp only [Option.some.injEq] at h
    subst h
    have := Finset.min'_mem _ hM
    rw [Finset.mem_filter] at this
    exact this

theorem pickBidder_none {v : Finset (Fin n) → ℝ} {s : State n}
    (h : pickBidder v s = none) : pool s = ∅ := by
  unfold pickBidder at h
  simp only at h
  split_ifs at h with hM
  by_contra hne
  rw [← ne_eq, ← Finset.nonempty_iff_ne_empty] at hne
  obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image (pool s)
    (fun j => marg v {j} s.cur.toFinset) hne
  exact hM ⟨i, Finset.mem_filter.2 ⟨hi, hmax⟩⟩

theorem mem_pool {s : State n} {i : Fin n} :
    i ∈ pool s ↔ i ∈ s.A ∧ i ∉ s.prev ∧ i ∉ s.cur := by
  unfold pool
  simp [Finset.mem_sdiff, Finset.mem_union, List.mem_toFinset, not_or]

/-- In-phase invariant relating the state `s0` at the start of a phase (with `s0.cur = []`) and
the current state `s`. -/
structure PhInv (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (B : ℝ) (s0 s : State n) : Prop where
  prev_eq : s.prev = s0.prev
  tgt_eq : s.tgt = s0.tgt
  t_eq : s.t = s0.t
  A_sub : s.A ⊆ s0.A
  nodup : s.cur.Nodup
  cur_A : ∀ i ∈ s.cur, i ∈ s.A
  cur_prev : ∀ i ∈ s.cur, i ∉ s.prev
  p_out : ∀ i, i ∉ s.cur → i ∈ s.A → s.p i = s0.p i
  p_le : ∀ i, s.p i ≤ s0.p i
  p_nn : ∀ i, 0 ≤ s0.p i → 0 ≤ s.p i
  p_cur : ∀ k (hk : k < s.cur.length), s.p s.cur[k] =
      min (s0.p s.cur[k]) (marg v {s.cur[k]} (s.cur.take k).toFinset * B / s.tgt) ∧
      c s.cur[k] ≤ s.p s.cur[k]
  rej : ∀ j ∈ s0.A, j ∉ s.A → j ∉ s0.prev ∧ ∃ k ≤ s.cur.length,
      v (s.cur.take k).toFinset < s.tgt ∧
      min (s0.p j) (marg v {j} (s.cur.take k).toFinset * B / s.tgt) < c j
  greedy : ∀ k (hk : k < s.cur.length), ∀ j ∈ pool s,
      marg v {j} (s.cur.take k).toFinset ≤ marg v {s.cur[k]} (s.cur.take k).toFinset
  greedy2 : ∀ k l (hl : l < s.cur.length) (hkl : k < l),
      marg v {s.cur[l]} (s.cur.take k).toFinset ≤
        marg v {s.cur[k]'(lt_trans hkl hl)} (s.cur.take k).toFinset
  below : ∀ k, k < s.cur.length → v (s.cur.take k).toFinset < s.tgt

theorem PhInv.init (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (B : ℝ) (s0 : State n)
    (h0 : s0.cur = []) : PhInv v c B s0 s0 := by
  refine ⟨rfl, rfl, rfl, le_rfl, ?_, ?_, ?_, fun _ _ _ => rfl, fun _ => le_rfl,
    fun _ h => h, ?_, fun j h1 h2 => absurd h1 h2, ?_, ?_, ?_⟩ <;> simp [h0]

theorem take_append_single_of_le {α : Type} (l : List α) (a : α) {k : ℕ} (hk : k ≤ l.length) :
    (l ++ [a]).take k = l.take k := List.take_append_of_le_length hk

theorem take_append_single_len {α : Type} (l : List α) (a : α) :
    (l ++ [a]).take l.length = l := by
  rw [take_append_single_of_le l a le_rfl, List.take_length]

theorem PhInv.step {v : Finset (Fin n) → ℝ} {c : Fin n → ℝ} {B : ℝ} {s0 s : State n} {i : Fin n}
    (hmono : IsMonotone v) (hB : 0 ≤ B) (htgt : 0 ≤ s0.tgt)
    (h : PhInv v c B s0 s) (hlt : v s.cur.toFinset < s.tgt) (hpick : pickBidder v s = some i) :
    PhInv v c B s0 (innerStep v c B s i) := by
  obtain ⟨hip, hmax⟩ := pickBidder_some hpick
  rw [mem_pool] at hip
  obtain ⟨hiA, hiprev, hicur⟩ := hip
  have hpi : s.p i = s0.p i := h.p_out i hicur hiA
  have hxnn : 0 ≤ s0.p i → 0 ≤ min (s.p i) (marg v {i} s.cur.toFinset * B / s.tgt) := by
    intro h0
    apply le_min (h.p_nn i h0)
    apply div_nonneg (mul_nonneg (marg_nonneg hmono _ _) hB)
    rw [h.tgt_eq]; exact htgt
  unfold innerStep
  simp only
  split_ifs with hacc
  · -- accept
    refine ⟨h.prev_eq, h.tgt_eq, h.t_eq, h.A_sub, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals dsimp only
    · exact List.nodup_append.2 ⟨h.nodup, List.nodup_singleton _,
        by intro a ha b hb; simp at hb; subst hb; intro e; subst e; exact hicur ha⟩
    · intro j hj
      rcases List.mem_append.1 hj with hj | hj
      · exact h.cur_A j hj
      · simp at hj; subst hj; exact hiA
    · intro j hj
      rcases List.mem_append.1 hj with hj | hj
      · exact h.cur_prev j hj
      · simp at hj; subst hj; exact hiprev
    · intro j hj hjA
      have hji : j ≠ i := by intro e; subst e; simp at hj
      rw [Function.update_of_ne hji]
      exact h.p_out j (fun hh => hj (List.mem_append_left _ hh)) hjA
    · intro j
      by_cases hji : j = i
      · subst hji; rw [Function.update_self, ← hpi]; exact min_le_left _ _
      · rw [Function.update_of_ne hji]; exact h.p_le j
    · intro j hj0
      by_cases hji : j = i
      · subst hji; rw [Function.update_self]; exact hxnn hj0
      · rw [Function.update_of_ne hji]; exact h.p_nn j hj0
    · intro k hk
      simp only [List.length_append, List.length_singleton] at hk
      rcases Nat.lt_or_ge k s.cur.length with hk' | hk'
      · rw [List.getElem_append_left hk', take_append_single_of_le _ _ hk'.le]
        have hne : s.cur[k] ≠ i := by intro e; rw [← e] at hicur; exact hicur (List.getElem_mem _)
        rw [Function.update_of_ne hne]
        exact h.p_cur k hk'
      · have hke : k = s.cur.length := by omega
        subst hke
        rw [List.getElem_concat_length rfl, take_append_single_len, Function.update_self, hpi]
        exact ⟨rfl, by rw [← hpi]; exact hacc⟩
    · intro j hj0 hjA
      obtain ⟨hjp, k, hk, h1, h2⟩ := h.rej j hj0 hjA
      refine ⟨hjp, k, by simp; omega, ?_⟩
      rw [take_append_single_of_le _ _ hk]
      exact ⟨h1, h2⟩
    · intro k hk j hj
      rw [mem_pool] at hj
      dsimp only at hj
      obtain ⟨hjA, hjprev, hjcur⟩ := hj
      have hjcur' : j ∉ s.cur := fun hh => hjcur (List.mem_append_left _ hh)
      have hji : j ≠ i := by intro e; subst e; exact hjcur (by simp)
      have hjpool : j ∈ pool s := mem_pool.2 ⟨hjA, hjprev, hjcur'⟩
      simp only [List.length_append, List.length_singleton] at hk
      rcases Nat.lt_or_ge k s.cur.length with hk' | hk'
      · rw [List.getElem_append_left hk', take_append_single_of_le _ _ hk'.le]
        exact h.greedy k hk' j hjpool
      · have hke : k = s.cur.length := by omega
        subst hke
        rw [List.getElem_concat_length rfl, take_append_single_len]
        exact hmax j hjpool
    · intro k l hl hkl
      simp only [List.length_append, List.length_singleton] at hl
      have hk' : k < s.cur.length := by omega
      rw [List.getElem_append_left hk', take_append_single_of_le _ _ hk'.le]
      rcases Nat.lt_or_ge l s.cur.length with hl' | hl'
      · rw [List.getElem_append_left hl']
        exact h.greedy2 k l hl' hkl
      · have hle : l = s.cur.length := by omega
        subst hle
        rw [List.getElem_concat_length rfl]
        exact h.greedy k hk' i (mem_pool.2 ⟨hiA, hiprev, hicur⟩)
    · intro k hk
      simp only [List.length_append, List.length_singleton] at hk
      rcases Nat.lt_or_ge k s.cur.length with hk' | hk'
      · rw [take_append_single_of_le _ _ hk'.le]; exact h.below k hk'
      · have hke : k = s.cur.length := by omega
        subst hke
        rw [take_append_single_len]; exact hlt
  · -- reject
    refine ⟨h.prev_eq, h.tgt_eq, h.t_eq, (Finset.erase_subset _ _).trans h.A_sub, h.nodup, ?_,
      h.cur_prev, ?_, ?_, ?_, ?_, ?_, ?_, h.greedy2, h.below⟩
    all_goals dsimp only
    · intro j hj
      have hji : j ≠ i := by intro e; subst e; exact hicur hj
      exact Finset.mem_erase.2 ⟨hji, h.cur_A j hj⟩
    · intro j hj hjA
      have hji : j ≠ i := (Finset.mem_erase.1 hjA).1
      rw [Function.update_of_ne hji]
      exact h.p_out j hj (Finset.mem_erase.1 hjA).2
    · intro j
      by_cases hji : j = i
      · subst hji; rw [Function.update_self, ← hpi]; exact min_le_left _ _
      · rw [Function.update_of_ne hji]; exact h.p_le j
    · intro j hj0
      by_cases hji : j = i
      · subst hji; rw [Function.update_self]; exact hxnn hj0
      · rw [Function.update_of_ne hji]; exact h.p_nn j hj0
    · intro k hk
      have hne : s.cur[k] ≠ i := by intro e; rw [← e] at hicur; exact hicur (List.getElem_mem _)
      rw [Function.update_of_ne hne]
      exact h.p_cur k hk
    · intro j hj0 hjA
      by_cases hji : j = i
      · subst hji
        refine ⟨by rw [← h.prev_eq]; exact hiprev, s.cur.length, le_rfl, ?_, ?_⟩
        · rw [List.take_length]; exact hlt
        · rw [List.take_length, ← hpi]; exact lt_of_not_ge hacc
      · exact h.rej j hj0 (fun hh => hjA (Finset.mem_erase.2 ⟨hji, hh⟩))
    · intro k hk j hj
      rw [mem_pool] at hj
      dsimp only at hj
      obtain ⟨hjA, hjprev, hjcur⟩ := hj
      exact h.greedy k hk j (mem_pool.2 ⟨(Finset.mem_erase.1 hjA).2, hjprev, hjcur⟩)

theorem pool_step {v : Finset (Fin n) → ℝ} {c : Fin n → ℝ} {B : ℝ} {s : State n} {i : Fin n}
    (hi : i ∈ pool s) : pool (innerStep v c B s i) = (pool s).erase i := by
  rw [mem_pool] at hi
  ext j
  rw [mem_pool, Finset.mem_erase, mem_pool]
  unfold innerStep
  simp only
  split_ifs
  · simp only [List.mem_append, List.mem_singleton, not_or]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩; exact ⟨h4, h1, h2, h3⟩
    · rintro ⟨h4, h1, h2, h3⟩; exact ⟨h1, h2, h3, h4⟩
  · simp only [Finset.mem_erase]
    constructor
    · rintro ⟨⟨h4, h1⟩, h2, h3⟩; exact ⟨h4, h1, h2, h3⟩
    · rintro ⟨h4, h1, h2, h3⟩; exact ⟨⟨h4, h1⟩, h2, h3⟩

/-- Stop condition of the inner loop. -/
def Stopped (v : Finset (Fin n) → ℝ) (s : State n) : Prop :=
  s.tgt ≤ v s.cur.toFinset ∨ pool s = ∅

theorem innerLoop_inv {v : Finset (Fin n) → ℝ} {c : Fin n → ℝ} {B : ℝ} {s0 : State n}
    (hmono : IsMonotone v) (hB : 0 ≤ B) (htgt : 0 ≤ s0.tgt) :
    ∀ (k : ℕ) (s : State n), PhInv v c B s0 s →
      PhInv v c B s0 (innerLoop v c B k s) ∧
        ((pool s).card ≤ k → Stopped v (innerLoop v c B k s)) := by
  intro k
  induction k with
  | zero =>
    intro s h
    refine ⟨h, fun hk => Or.inr ?_⟩
    exact Finset.card_eq_zero.1 (Nat.le_zero.1 hk)
  | succ k ih =>
    intro s h
    unfold innerLoop
    split_ifs with hstop
    · exact ⟨h, fun _ => Or.inl hstop⟩
    · cases hp : pickBidder v s with
      | none => exact ⟨h, fun _ => Or.inr (pickBidder_none hp)⟩
      | some i =>
        simp only
        have h' := h.step hmono hB htgt (lt_of_not_ge hstop) hp
        obtain ⟨h1, h2⟩ := ih _ h'
        refine ⟨h1, fun hk => h2 ?_⟩
        have hi := (pickBidder_some hp).1
        rw [pool_step hi, Finset.card_erase_of_mem hi]
        omega

/-! ## Phases -/

/-- The state after line 3 of a phase. -/
def reset (s : State n) : State n :=
  { s with t := s.t + 1, tgt := 2 * s.tgt, prev := s.cur, cur := [] }

theorem phase_eq (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (B : ℝ) (s : State n) :
    phase v c B s = innerLoop v c B n (reset s) := rfl

theorem phase_inv {v : Finset (Fin n) → ℝ} {c : Fin n → ℝ} {B : ℝ} (s : State n)
    (hmono : IsMonotone v) (hB : 0 ≤ B) (htgt : 0 ≤ s.tgt) :
    PhInv v c B (reset s) (phase v c B s) ∧ Stopped v (phase v c B s) := by
  have h0 : 0 ≤ (reset s).tgt := by simp [reset]; linarith
  obtain ⟨h1, h2⟩ := innerLoop_inv (c := c) hmono hB h0 n (reset s) (PhInv.init v c B _ rfl)
  refine ⟨h1, h2 ?_⟩
  have := Finset.card_le_univ (pool (reset s))
  simpa using this

end BCMCore

namespace BCMCore
open BudgetClock.Monotone

variable {n : ℕ}

/-! ## The run -/

/-- `PS k` is the state after `k` outer iterations, i.e. `phaseState (k+1)`. -/
noncomputable def PS (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (B : ℝ) (k : ℕ) : State n :=
  (outerStep v c B)^[k] (initState v B)

theorem PS_zero (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (B : ℝ) :
    PS v c B 0 = initState v B := rfl

theorem PS_succ (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (B : ℝ) (k : ℕ) :
    PS v c B (k + 1) = outerStep v c B (PS v c B k) := by
  unfold PS; rw [Function.iterate_succ_apply']

theorem phaseState_eq (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (B : ℝ) (t : ℕ) :
    phaseState v c B t = PS v c B (t - 1) := rfl

theorem finalState_eq (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (B : ℝ) :
    finalState v c B = PS v c B (n + 2) := rfl

theorem innerStep_t (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (B : ℝ) (s : State n)
    (i : Fin n) : (innerStep v c B s i).t = s.t := by
  unfold innerStep; simp only; split_ifs <;> rfl

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

theorem phase_t (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (B : ℝ) (s : State n) :
    (phase v c B s).t = s.t + 1 := by
  rw [phase_eq, innerLoop_t]; rfl

theorem outerStep_cases (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (B : ℝ) (s : State n) :
    ((pool s).Nonempty ∧ outerStep v c B s = phase v c B s) ∨
      (pool s = ∅ ∧ outerStep v c B s = s) := by
  unfold outerStep
  by_cases h : (pool s).Nonempty
  · left; exact ⟨h, by rw [if_pos h]⟩
  · right; exact ⟨Finset.not_nonempty_iff_eq_empty.1 h, by rw [if_neg h]⟩

theorem PS_t_succ (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (B : ℝ) (k : ℕ) :
    ((pool (PS v c B k)).Nonempty ∧ PS v c B (k + 1) = phase v c B (PS v c B k) ∧
        (PS v c B (k + 1)).t = (PS v c B k).t + 1) ∨
      (pool (PS v c B k) = ∅ ∧ PS v c B (k + 1) = PS v c B k) := by
  rw [PS_succ]
  rcases outerStep_cases v c B (PS v c B k) with ⟨h1, h⟩ | ⟨h1, h⟩
  · left; exact ⟨h1, h, by rw [h, phase_t]⟩
  · right; exact ⟨h1, h⟩

theorem PS_stable (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (B : ℝ) {k : ℕ}
    (h : pool (PS v c B k) = ∅) : ∀ j, k ≤ j → PS v c B j = PS v c B k := by
  intro j hj
  induction j with
  | zero => rw [Nat.le_zero.1 hj]
  | succ j ih =>
    rcases Nat.lt_or_ge k (j + 1) with h' | h'
    · have e := ih (Nat.lt_succ_iff.1 h')
      rcases PS_t_succ v c B j with ⟨hn, _, _⟩ | ⟨_, h2⟩
      · rw [e, h] at hn; simp at hn
      · rw [h2, e]
    · rw [le_antisymm hj h']

theorem PS_t_le (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (B : ℝ) (k : ℕ) :
    1 ≤ (PS v c B k).t ∧ (PS v c B k).t ≤ k + 1 := by
  induction k with
  | zero => simp [PS_zero, initState]
  | succ k ih =>
    rcases PS_t_succ v c B k with ⟨_, _, h⟩ | ⟨_, h⟩
    · rw [h]; omega
    · rw [h]; omega

theorem PS_t_lt (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (B : ℝ) (k : ℕ) :
    (PS v c B k).t < k + 1 → pool (PS v c B k) = ∅ := by
  induction k with
  | zero => intro h; simp [PS_zero, initState] at h
  | succ k ih =>
    intro h
    rcases PS_t_succ v c B k with ⟨hn, he, ht⟩ | ⟨hp, he⟩
    · have : (PS v c B k).t < k + 1 := by omega
      rw [ih this] at hn; simp at hn
    · rw [he]; exact hp

theorem lastPhase_eq (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (B : ℝ) :
    lastPhase v c B = (PS v c B (n + 2)).t := rfl

theorem lastPhase_ge (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (B : ℝ) :
    1 ≤ lastPhase v c B ∧ lastPhase v c B ≤ n + 3 := by
  rw [lastPhase_eq]; exact PS_t_le v c B (n + 2)

theorem PS_t_of_le_last (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (B : ℝ) {k : ℕ}
    (hk : k + 1 ≤ lastPhase v c B) : (PS v c B k).t = k + 1 := by
  have hb := PS_t_le v c B k
  by_contra hne
  have hlt : (PS v c B k).t < k + 1 := by omega
  have hp := PS_t_lt v c B k hlt
  rw [lastPhase_eq] at hk
  rcases Nat.lt_or_ge (n + 2) k with h | h
  · have := (PS_t_le v c B (n + 2)).2; omega
  · rw [PS_stable v c B hp (n + 2) h] at hk; omega

/-- For `k + 2 ≤ t̂`, outer iteration `k+1` runs a phase. -/
theorem PS_runs (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (B : ℝ) {k : ℕ}
    (hk : k + 2 ≤ lastPhase v c B) :
    (pool (PS v c B k)).Nonempty ∧ PS v c B (k + 1) = phase v c B (PS v c B k) := by
  have h1 := PS_t_of_le_last v c B (k := k + 1) hk
  have h0 := PS_t_of_le_last v c B (k := k) (by omega)
  rcases PS_t_succ v c B k with ⟨hn, he, _⟩ | ⟨_, he⟩
  · exact ⟨hn, he⟩
  · rw [he] at h1; omega

theorem PS_t_mono (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (B : ℝ) (j : ℕ) :
    ∀ d, (PS v c B j).t ≤ (PS v c B (j + d)).t := by
  intro d
  induction d with
  | zero => exact le_rfl
  | succ d ih =>
    rcases PS_t_succ v c B (j + d) with ⟨_, _, h4⟩ | ⟨_, h4⟩
    · rw [← add_assoc, h4]; omega
    · rw [← add_assoc, h4]; exact ih

theorem PS_last (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (B : ℝ) :
    PS v c B (lastPhase v c B - 1) = finalState v c B := by
  have hl := lastPhase_ge v c B
  rw [finalState_eq]
  have ht := PS_t_of_le_last v c B (k := lastPhase v c B - 1) (by omega)
  rcases Nat.lt_or_ge (lastPhase v c B - 1) (n + 2) with h | h
  · have hp : pool (PS v c B (lastPhase v c B - 1)) = ∅ := by
      by_contra hne
      rw [← ne_eq, ← Finset.nonempty_iff_ne_empty] at hne
      rcases PS_t_succ v c B (lastPhase v c B - 1) with ⟨_, _, h2⟩ | ⟨h3, _⟩
      · have := PS_t_mono v c B (lastPhase v c B - 1 + 1) (n + 2 - (lastPhase v c B - 1 + 1))
        rw [show lastPhase v c B - 1 + 1 + (n + 2 - (lastPhase v c B - 1 + 1)) = n + 2 by omega,
          ← lastPhase_eq] at this
        omega
      · rw [h3] at hne; simp at hne
    exact (PS_stable v c B hp (n + 2) h.le).symm
  · have : lastPhase v c B - 1 = n + 2 := by omega
    rw [this]

/-! ## Global invariant -/

/-- `m = OP̃T_1 = v(S_1)`. -/
noncomputable def mval (v : Finset (Fin n) → ℝ) (B : ℝ) : ℝ := (initState v B).tgt

theorem single_le_mval (v : Finset (Fin n) → ℝ) (B : ℝ) : ∀ j, v {j} ≤ mval v B := by
  intro j
  unfold mval initState
  simp only
  split_ifs with hM
  · have := Finset.min'_mem _ hM
    rw [Finset.mem_filter] at this
    simpa using this.2 j
  · exfalso
    obtain ⟨i, _, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin n))
      (fun j => v {j}) ⟨j, Finset.mem_univ _⟩
    exact hM ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, fun k => hmax k (Finset.mem_univ _)⟩⟩

theorem mval_nonneg {v : Finset (Fin n) → ℝ} (hv : ∀ S, 0 ≤ v S) (B : ℝ) : 0 ≤ mval v B :=
  hv _

structure GInv (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (B : ℝ) (s : State n) : Prop where
  t1 : 1 ≤ s.t
  tgt : s.tgt = 2 ^ (s.t - 1) * mval v B
  cost : ∀ i ∈ s.A, c i ≤ s.p i ∨ s.p i = B
  p_nn : ∀ i, 0 ≤ s.p i
  p_le : ∀ i, s.p i ≤ B
  prev_nodup : s.prev.Nodup
  cur_nodup : s.cur.Nodup
  disj : ∀ i ∈ s.cur, i ∉ s.prev
  prev_A : ∀ i ∈ s.prev, i ∈ s.A
  cur_A : ∀ i ∈ s.cur, i ∈ s.A

theorem GInv.init (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) {B : ℝ} (hB : 0 ≤ B) :
    GInv v c B (initState v B) := by
  refine ⟨by simp [initState], by simp [initState, mval], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i _; right; rfl
  · intro i; exact hB
  · intro i; exact le_rfl
  · simp [initState]
  · unfold initState; simp only; split_ifs <;> simp
  · simp [initState]
  · simp [initState]
  · simp [initState]

theorem GInv.stepPhase {v : Finset (Fin n) → ℝ} {c : Fin n → ℝ} {B : ℝ} {s : State n}
    (hv : ∀ S, 0 ≤ v S) (hmono : IsMonotone v) (hB : 0 ≤ B) (h : GInv v c B s) :
    GInv v c B (phase v c B s) := by
  have htgt : 0 ≤ s.tgt := by
    rw [h.tgt]; exact mul_nonneg (by positivity) (mval_nonneg hv B)
  obtain ⟨hI, _⟩ := phase_inv (c := c) s hmono hB htgt
  have hpe : (phase v c B s).prev = s.cur := hI.prev_eq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hI.nodup, ?_, ?_, hI.cur_A⟩
  · rw [hI.t_eq]; simp [reset]
  · rw [hI.tgt_eq, hI.t_eq]; simp only [reset]; rw [h.tgt]
    have := h.t1
    obtain ⟨j, hj⟩ : ∃ j, s.t = j + 1 := ⟨s.t - 1, by omega⟩
    rw [hj]; simp [pow_succ]; ring
  · intro i hi
    by_cases hc : i ∈ (phase v c B s).cur
    · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hc
      left; exact (hI.p_cur k hk).2
    · rw [hI.p_out i hc hi]
      exact h.cost i (hI.A_sub hi)
  · intro i; exact hI.p_nn i (h.p_nn i)
  · intro i; exact (hI.p_le i).trans (h.p_le i)
  · rw [hpe]; exact h.cur_nodup
  · intro i hi; rw [hpe]; have := hI.cur_prev i hi; rwa [hpe] at this
  · intro i hi
    rw [hpe] at hi
    by_contra hn
    have := (hI.rej i (h.cur_A i hi) hn).1
    exact this hi

theorem GInv.all {v : Finset (Fin n) → ℝ} {c : Fin n → ℝ} {B : ℝ}
    (hv : ∀ S, 0 ≤ v S) (hmono : IsMonotone v) (hB : 0 ≤ B) : ∀ k, GInv v c B (PS v c B k) := by
  intro k
  induction k with
  | zero => exact GInv.init v c hB
  | succ k ih =>
    rcases PS_t_succ v c B k with ⟨_, he, _⟩ | ⟨_, he⟩
    · rw [he]; exact ih.stepPhase hv hmono hB
    · rw [he]; exact ih

theorem PS_A_succ (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (B : ℝ) (hmono : IsMonotone v)
    (hv : ∀ S, 0 ≤ v S) (hB : 0 ≤ B) (k : ℕ) :
    (PS v c B (k + 1)).A ⊆ (PS v c B k).A := by
  rcases PS_t_succ v c B k with ⟨_, he, _⟩ | ⟨_, he⟩
  · rw [he]
    have g := GInv.all (c := c) hv hmono hB k
    have htgt : 0 ≤ (PS v c B k).tgt := by
      rw [g.tgt]; exact mul_nonneg (by positivity) (mval_nonneg hv B)
    exact (phase_inv (c := c) _ hmono hB htgt).1.A_sub
  · rw [he]

/-- Phase facts: for `2 ≤ t ≤ t̂` (here `t = k + 2`), the state at the end of phase `t` is the phase
run from the state at the end of phase `t - 1`. -/
theorem phase_facts {v : Finset (Fin n) → ℝ} {c : Fin n → ℝ} {B : ℝ}
    (hv : ∀ S, 0 ≤ v S) (hmono : IsMonotone v) (hB : 0 ≤ B) {k : ℕ}
    (hk : k + 2 ≤ lastPhase v c B) :
    PhInv v c B (reset (PS v c B k)) (PS v c B (k + 1)) ∧ Stopped v (PS v c B (k + 1)) := by
  obtain ⟨_, he⟩ := PS_runs v c B hk
  rw [he]
  have g := GInv.all (c := c) hv hmono hB k
  have htgt : 0 ≤ (PS v c B k).tgt := by
    rw [g.tgt]; exact mul_nonneg (by positivity) (mval_nonneg hv B)
  exact phase_inv _ hmono hB htgt

theorem PS_t_tgt {v : Finset (Fin n) → ℝ} {c : Fin n → ℝ} {B : ℝ}
    (hv : ∀ S, 0 ≤ v S) (hmono : IsMonotone v) (hB : 0 ≤ B) {k : ℕ}
    (hk : k + 1 ≤ lastPhase v c B) :
    (PS v c B k).t = k + 1 ∧ (PS v c B k).tgt = 2 ^ k * mval v B := by
  have ht := PS_t_of_le_last v c B hk
  refine ⟨ht, ?_⟩
  rw [(GInv.all (c := c) hv hmono hB k).tgt, ht]; simp

/-- Termination: if `m > 0` the final pool is empty. -/
theorem final_pool_empty {v : Finset (Fin n) → ℝ} {c : Fin n → ℝ} {B : ℝ}
    (hv : ∀ S, 0 ≤ v S) (hmono : IsMonotone v) (hsub : NonmonotoneSubmod.Shared.Submodular v)
    (hB : 0 ≤ B) (hm : 0 < mval v B) : pool (finalState v c B) = ∅ := by
  by_cases hn : n = 0
  · subst hn; ext x; exact x.elim0
  rw [finalState_eq]
  have hb := PS_t_le v c B (n + 2)
  rcases Nat.lt_or_ge (PS v c B (n + 2)).t (n + 3) with h | h
  · exact PS_t_lt v c B (n + 2) h
  · have hl : n + 3 ≤ lastPhase v c B := by rw [lastPhase_eq]; omega
    have hf := (phase_facts (c := c) hv hmono hB (k := n + 1) (by omega)).2
    rcases hf with hf | hf
    · exfalso
      have htg := (PS_t_tgt (c := c) hv hmono hB (k := n + 2) (by omega)).2
      rw [htg] at hf
      have hm1 := single_le_mval v B
      have hcard : v (PS v c B (n + 2)).cur.toFinset ≤ n * mval v B := by
        by_cases hne : (PS v c B (n + 2)).cur.toFinset.Nonempty
        · have := val_le_card hv hsub _ hm1 _ hne
          have hc : ((PS v c B (n + 2)).cur.toFinset.card : ℝ) ≤ n := by
            have := Finset.card_le_univ (PS v c B (n + 2)).cur.toFinset
            simp at this; exact_mod_cast this
          nlinarith
        · rw [Finset.not_nonempty_iff_eq_empty] at hne
          rw [hne]
          let i0 : Fin n := ⟨0, by omega⟩
          have := hmono ∅ {i0} (Finset.empty_subset _)
          have := hm1 i0
          have : (1 : ℝ) ≤ n := by
            have : 1 ≤ n := by omega
            exact_mod_cast this
          nlinarith
      have h2 : (n : ℝ) < 2 ^ (n + 2) := by
        have : n < 2 ^ (n + 2) := by
          calc n < 2 ^ n := Nat.lt_two_pow_self
            _ ≤ 2 ^ (n + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
        exact_mod_cast this
      nlinarith
    · exact hf

end BCMCore

namespace BCMCore
open BudgetClock.Monotone

variable {n : ℕ}

theorem dropLast_getElem {α : Type} (l : List α) (j : ℕ) (hj : j < l.dropLast.length) :
    l.dropLast[j] = l[j]'(by simp at hj; omega) := by
  simp [List.getElem_dropLast]

theorem dropLast_take {α : Type} (l : List α) (j : ℕ) (hj : j < l.dropLast.length) :
    l.dropLast.take j = l.take j := by
  rw [List.dropLast_eq_take, List.take_take]
  congr 1
  simp at hj
  omega

theorem dropLast_eq_take' {α : Type} (l : List α) : l.dropLast = l.take (l.length - 1) :=
  List.dropLast_eq_take

/-- Prices of a phase list satisfy `p τ ≤ B · marg` (for `τ > 0`). -/
theorem PhInv.price_le {v : Finset (Fin n) → ℝ} {c : Fin n → ℝ} {B : ℝ} {s0 s : State n}
    (h : PhInv v c B s0 s) (htgt : 0 < s.tgt) (k : ℕ) (hk : k < s.cur.length) :
    s.p s.cur[k] * s.tgt ≤ B * marg v {s.cur[k]} (s.cur.take k).toFinset := by
  have h1 := (h.p_cur k hk).1
  have h2 : s.p s.cur[k] ≤ marg v {s.cur[k]} (s.cur.take k).toFinset * B / s.tgt := by
    rw [h1]; exact min_le_right _ _
  rw [le_div_iff₀ htgt] at h2
  linarith

theorem PhInv.tgt_pos {v : Finset (Fin n) → ℝ} {c : Fin n → ℝ} {B : ℝ} {s0 s : State n}
    (hv : ∀ S, 0 ≤ v S) (h : PhInv v c B s0 s) (hne : s.cur ≠ []) : 0 < s.tgt := by
  have hl : 0 < s.cur.length := List.length_pos_iff.2 hne
  have := h.below 0 hl
  have := hv (s.cur.take 0).toFinset
  linarith

theorem PhInv.cost_dropLast {v : Finset (Fin n) → ℝ} {c : Fin n → ℝ} {B : ℝ} {s0 s : State n}
    (hv : ∀ S, 0 ≤ v S) (hB : 0 ≤ B) (h : PhInv v c B s0 s) :
    listCost s.p s.cur.dropLast ≤ B := by
  by_cases hne : s.cur = []
  · rw [hne]; simp [listCost]; exact hB
  have htgt := h.tgt_pos hv hne
  have hl : 0 < s.cur.length := List.length_pos_iff.2 hne
  have key := cost_le_of_marg (v := v) (p := s.p) (τ := s.tgt) (B := B) s.cur.dropLast
    (by
      intro k hk
      rw [dropLast_getElem _ k hk, dropLast_take _ k hk]
      have hk' : k < s.cur.length := by simp at hk; omega
      exact h.price_le htgt k hk')
  have hb : v s.cur.dropLast.toFinset < s.tgt := by
    rw [List.dropLast_eq_take]; exact h.below _ (by omega)
  have := hv ∅
  have h3 : listCost s.p s.cur.dropLast * s.tgt ≤ B * s.tgt := by nlinarith
  exact le_of_mul_le_mul_right h3 htgt

/-! ## Pruning -/

theorem prune_cases (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) {B : ℝ} (hB : 0 ≤ B) (s : State n) :
    (¬ B < listCost s.p s.prev ∧ prune v c B s = (s.prev, s.cur, s.p)) ∨
    (B < listCost s.p s.prev ∧ ∃ j, s.prev.getLast? = some j ∧
      let x := min (s.p j) (marg v {j} s.cur.toFinset * B / s.tgt)
      ((c j ≤ x ∧ prune v c B s = (s.prev.dropLast, s.cur ++ [j], Function.update s.p j x)) ∨
       (¬ c j ≤ x ∧ prune v c B s = (s.prev.dropLast, s.cur, Function.update s.p j x)))) := by
  unfold prune
  by_cases hb : B < listCost s.p s.prev
  · right
    refine ⟨hb, ?_⟩
    rw [if_pos hb]
    cases hl : s.prev.getLast? with
    | none =>
      exfalso
      rw [List.getLast?_eq_none_iff] at hl
      rw [hl] at hb; simp [listCost] at hb
      linarith
    | some j =>
      refine ⟨j, rfl, ?_⟩
      simp only
      split_ifs with hc
      · left; exact ⟨hc, rfl⟩
      · right; exact ⟨hc, rfl⟩
  · left; exact ⟨hb, by rw [if_neg hb]⟩

end BCMCore

namespace BCMCore
open BudgetClock.Monotone

variable {n : ℕ}

theorem subadd_norm {v : Finset (Fin n) → ℝ} (hmono : IsMonotone v)
    (hsub : NonmonotoneSubmod.Shared.Submodular v) (S T : Finset (Fin n)) :
    v (S ∪ T) - v ∅ ≤ (v S - v ∅) + (v T - v ∅) := by
  have := hsub S T
  have := hmono ∅ (S ∩ T) (Finset.empty_subset _)
  linarith

theorem subadd_biUnion' {v : Finset (Fin n) → ℝ} (hmono : IsMonotone v)
    (hsub : NonmonotoneSubmod.Shared.Submodular v) {ι : Type} [DecidableEq ι]
    (I : Finset ι) (f : ι → Finset (Fin n)) :
    v (I.biUnion f) - v ∅ ≤ ∑ k ∈ I, (v (f k) - v ∅) := by
  induction I using Finset.induction_on with
  | empty => simp
  | insert a I ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    have := subadd_norm hmono hsub (f a) (I.biUnion f)
    linarith

theorem PS_A_mono {v : Finset (Fin n) → ℝ} {c : Fin n → ℝ} {B : ℝ} (hmono : IsMonotone v)
    (hv : ∀ S, 0 ≤ v S) (hB : 0 ≤ B) {j k : ℕ} (hjk : j ≤ k) :
    (PS v c B k).A ⊆ (PS v c B j).A := by
  induction k with
  | zero => rw [Nat.le_zero.1 hjk]
  | succ k ih =>
    rcases Nat.lt_or_ge j (k + 1) with h | h
    · exact (PS_A_succ v c B hmono hv hB k).trans (ih (Nat.lt_succ_iff.1 h))
    · rw [le_antisymm hjk h]

theorem PS_t_mono' (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (B : ℝ) {j k : ℕ} (hjk : j ≤ k) :
    (PS v c B j).t ≤ (PS v c B k).t := by
  have := PS_t_mono v c B j (k - j)
  rwa [show j + (k - j) = k by omega] at this

/-- A bidder removed by the end of outer iteration `K` was removed in some phase `k' + 1` with
`1 ≤ k' ≤ K` and `k' + 1 ≤ t̂`. -/
theorem rej_phase {v : Finset (Fin n) → ℝ} {c : Fin n → ℝ} {B : ℝ} (hmono : IsMonotone v)
    (hv : ∀ S, 0 ≤ v S) (hB : 0 ≤ B) {j : Fin n} {K : ℕ} (hK : K ≤ n + 2)
    (hj : j ∉ (PS v c B K).A) :
    ∃ k', 1 ≤ k' ∧ k' ≤ K ∧ k' + 1 ≤ lastPhase v c B ∧ j ∈ (PS v c B (k' - 1)).A ∧
      j ∉ (PS v c B k').A := by
  classical
  have hex : ∃ k, j ∉ (PS v c B k).A := ⟨K, hj⟩
  let k' := Nat.find hex
  have hk'1 : j ∉ (PS v c B k').A := Nat.find_spec hex
  have hk'K : k' ≤ K := Nat.find_min' hex hj
  have hk'0 : k' ≠ 0 := by
    intro h0
    rw [h0] at hk'1
    exact hk'1 (by simp [PS_zero, initState])
  have hprev : j ∈ (PS v c B (k' - 1)).A := by
    by_contra h
    exact Nat.find_min hex (show k' - 1 < k' by omega) h
  refine ⟨k', by omega, hk'K, ?_, hprev, hk'1⟩
  have hs := PS_t_succ v c B (k' - 1)
  rw [show k' - 1 + 1 = k' by omega] at hs
  rcases hs with ⟨hn, _, ht⟩ | ⟨_, he⟩
  · have ht0 : (PS v c B (k' - 1)).t = k' := by
      have hb := PS_t_le v c B (k' - 1)
      by_contra hne
      have := PS_t_lt v c B (k' - 1) (by omega)
      rw [this] at hn; simp at hn
    have := PS_t_mono' v c B (show k' ≤ n + 2 by omega)
    rw [lastPhase_eq]; omega
  · rw [he] at hk'1; exact absurd hprev hk'1

/-- The rejection record of a bidder removed in phase `k' + 1`. -/
theorem rej_record {v : Finset (Fin n) → ℝ} {c : Fin n → ℝ} {B : ℝ} (hmono : IsMonotone v)
    (hv : ∀ S, 0 ≤ v S) (hB : 0 < B) (hm : 0 < mval v B) {j : Fin n} {k' : ℕ} (hk1 : 1 ≤ k')
    (hkL : k' + 1 ≤ lastPhase v c B) (hjA : j ∈ (PS v c B (k' - 1)).A)
    (hjA' : j ∉ (PS v c B k').A) (hcB : c j ≤ B) :
    ∃ i ≤ (PS v c B k').cur.length,
      v ((PS v c B k').cur.take i).toFinset < 2 ^ k' * mval v B ∧
      marg v {j} ((PS v c B k').cur.take i).toFinset * B < c j * (2 ^ k' * mval v B) := by
  obtain ⟨hI, _⟩ := phase_facts (c := c) hv hmono hB.le (k := k' - 1) (by omega)
  rw [show k' - 1 + 1 = k' by omega] at hI
  have htg := (PS_t_tgt (c := c) hv hmono hB.le (k := k') (by omega)).2
  have g := GInv.all (c := c) hv hmono hB.le (k' - 1)
  obtain ⟨_, i, hi, h1, h2⟩ := hI.rej j hjA hjA'
  refine ⟨i, hi, by rw [← htg]; exact h1, ?_⟩
  have hτ : 0 < (PS v c B k').tgt := by rw [htg]; positivity
  have hcost := g.cost j hjA
  have key : marg v {j} ((PS v c B k').cur.take i).toFinset * B / (PS v c B k').tgt < c j := by
    simp only [reset] at h2
    rcases lt_or_ge ((PS v c B (k' - 1)).p j) (marg v {j} ((PS v c B k').cur.take i).toFinset *
        B / (PS v c B k').tgt) with hlt | hge
    · rw [min_eq_left hlt.le] at h2
      rcases hcost with hc | hc
      · linarith
      · rw [hc] at h2; linarith
    · rwa [min_eq_right hge] at h2
  rw [div_lt_iff₀ hτ] at key
  rw [← htg]; linarith

/-- For a phase `t = k + 1 < t̂` (with `t ≥ 2`), the phase reached its target. -/
theorem phase_reached {v : Finset (Fin n) → ℝ} {c : Fin n → ℝ} {B : ℝ} (hmono : IsMonotone v)
    (hv : ∀ S, 0 ≤ v S) (hB : 0 ≤ B) {k : ℕ} (hk : k + 2 ≤ lastPhase v c B) :
    (PS v c B k).tgt ≤ v (PS v c B k).cur.toFinset := by
  rcases k with _ | k
  · simp [PS_zero, initState]
  · have hf := (phase_facts (c := c) hv hmono hB (k := k) (by omega)).2
    rcases hf with hf | hf
    · exact hf
    · exfalso
      have := (PS_runs v c B (k := k + 1) hk).1
      rw [hf] at this; simp at this

theorem take_sub_dropLast {α : Type} [DecidableEq α] (l : List α) (i : ℕ) (hi : i < l.length) :
    (l.take i).toFinset ⊆ l.dropLast.toFinset := by
  rw [List.dropLast_eq_take]
  intro x hx
  simp only [List.mem_toFinset] at hx ⊢
  have : l.take i = (l.take (l.length - 1)).take i := by rw [List.take_take]; congr 1; omega
  rw [this] at hx
  exact List.mem_of_mem_take hx

end BCMCore

namespace BCMCore
open BudgetClock.Monotone

variable {n : ℕ}

theorem v_empty_le_mval {v : Finset (Fin n) → ℝ} (hmono : IsMonotone v) (B : ℝ) :
    v ∅ ≤ mval v B := by
  by_cases hn : n = 0
  · subst hn
    unfold mval initState; simp only
    split_ifs with hM
    · exact (hM.choose).elim0
    · simp
  · let i0 : Fin n := ⟨0, by omega⟩
    exact (hmono ∅ {i0} (Finset.empty_subset _)).trans (single_le_mval v B i0)

theorem v_zero_of_mval_zero {v : Finset (Fin n) → ℝ} (hv : ∀ S, 0 ≤ v S) (hmono : IsMonotone v)
    (hsub : NonmonotoneSubmod.Shared.Submodular v) {B : ℝ} (hm : mval v B = 0) :
    ∀ S, v S = 0 := by
  intro S
  by_cases hS : S.Nonempty
  · have := val_le_card hv hsub (mval v B) (single_le_mval v B) S hS
    rw [hm, mul_zero] at this
    exact le_antisymm this (hv S)
  · rw [Finset.not_nonempty_iff_eq_empty] at hS
    subst hS
    have := v_empty_le_mval hmono (v := v) B
    rw [hm] at this
    exact le_antisymm this (hv _)

theorem final_eq {v : Finset (Fin n) → ℝ} {c : Fin n → ℝ} {B : ℝ} :
    finalState v c B = PS v c B (lastPhase v c B - 1) := (PS_last v c B).symm

theorem final_prev {v : Finset (Fin n) → ℝ} {c : Fin n → ℝ} {B : ℝ} (hv : ∀ S, 0 ≤ v S)
    (hmono : IsMonotone v) (hB : 0 ≤ B) (hL : 2 ≤ lastPhase v c B) :
    (finalState v c B).prev = (PS v c B (lastPhase v c B - 2)).cur ∧
      ∀ i ∈ (finalState v c B).prev, (finalState v c B).p i = (PS v c B (lastPhase v c B - 2)).p i := by
  rw [final_eq]
  obtain ⟨hI, _⟩ := phase_facts (c := c) hv hmono hB (k := lastPhase v c B - 2) (by omega)
  rw [show lastPhase v c B - 2 + 1 = lastPhase v c B - 1 by omega] at hI
  have g := GInv.all (c := c) hv hmono hB (lastPhase v c B - 1)
  have hpe : (PS v c B (lastPhase v c B - 1)).prev = (PS v c B (lastPhase v c B - 2)).cur :=
    hI.prev_eq
  refine ⟨hpe, fun i hi => ?_⟩
  have hic : i ∉ (PS v c B (lastPhase v c B - 1)).cur := fun h => hI.cur_prev i h hi
  exact hI.p_out i hic (g.prev_A i hi)

theorem geom_sum (N : ℕ) (hN : 1 ≤ N) : ∑ t ∈ Finset.Icc 2 N, (2:ℝ) ^ (t - 1) = 2 ^ N - 2 := by
  induction N with
  | zero => omega
  | succ N ih =>
    rcases Nat.lt_or_ge N 1 with h | h
    · have : N = 0 := by omega
      subst this; simp
    · rw [Finset.sum_Icc_succ_top (by omega), ih h]
      rw [show N + 1 - 1 = N by omega, pow_succ]; ring

theorem pool_empty_mem {s : State n} (hp : pool s = ∅) {j : Fin n} (hj : j ∈ s.A) :
    j ∈ s.prev ∨ j ∈ s.cur := by
  by_contra h
  rw [not_or] at h
  have : j ∈ pool s := mem_pool.2 ⟨hj, h.1, h.2⟩
  rw [hp] at this; simp at this

theorem mem_of_not_mem_dropLast {α : Type} {l : List α} {a j : α} (hl : l.getLast? = some a)
    (hj : j ∈ l) (hj' : j ∉ l.dropLast) : j = a := by
  have hne : l ≠ [] := by intro h; rw [h] at hl; simp at hl
  have e := List.dropLast_append_getLast hne
  rw [List.getLast?_eq_some_getLast hne, Option.some.injEq] at hl
  rw [← e, List.mem_append] at hj
  rcases hj with hj | hj
  · exact absurd hj hj'
  · simp at hj; rw [hj, hl]

/-- **Lemma 2** (for `t̂ ≥ 3`). -/
theorem lemma2_core {v : Finset (Fin n) → ℝ} (hv : ∀ S, 0 ≤ v S) (hmono : IsMonotone v)
    (hsub : NonmonotoneSubmod.Shared.Submodular v) (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i)
    (B : ℝ) (hB : 0 < B) (h3 : 3 ≤ lastPhase v c B) :
    ∀ Q : Finset (Fin n),
      Q ⊆ Finset.univ \ ((W1 v c B).toFinset ∪ (W2bar v c B).toFinset) →
      ∑ i ∈ Q, c i ≤ B →
      marg v Q ((W1 v c B).toFinset ∪ (W2bar v c B).toFinset) ≤
        (3 / 2 - 1 / (2 : ℝ) ^ (lastPhase v c B - 2)) * target v c B (lastPhase v c B) := by
  intro Q hQ hQc
  have htarget : target v c B (lastPhase v c B) = 2 ^ (lastPhase v c B - 1) * mval v B := by
    unfold target; rw [phaseState_eq]
    exact (PS_t_tgt (c := c) hv hmono hB.le (k := lastPhase v c B - 1) (by omega)).2
  -- the degenerate case `m = 0`
  rcases (mval_nonneg hv B).lt_or_eq with hm | hm
  swap
  · have h0 := v_zero_of_mval_zero hv hmono hsub hm.symm
    rw [htarget, ← hm]; unfold marg; rw [h0, h0]; simp
  set W := (W1 v c B).toFinset ∪ (W2bar v c B).toFinset with hW
  set m := mval v B with hmdef
  obtain ⟨l, hl⟩ : ∃ l, lastPhase v c B = l + 3 := ⟨lastPhase v c B - 3, by omega⟩
  -- the final state
  set sF := finalState v c B with hsF
  have hsFeq : sF = PS v c B (l + 2) := by rw [hsF, final_eq, hl, show l + 3 - 1 = l + 2 by omega]
  have hLn := (lastPhase_ge v c B).2
  obtain ⟨hprev, hprevp⟩ := final_prev (c := c) hv hmono hB.le (by omega)
  rw [← hsF, hl, show l + 3 - 2 = l + 1 by omega] at hprev hprevp
  have gF := GInv.all (c := c) hv hmono hB.le (l + 2)
  rw [← hsFeq] at gF
  have hpool : pool sF = ∅ := final_pool_empty hv hmono hsub hB.le hm
  have hcB : ∀ j ∈ Q, c j ≤ B := fun j hj =>
    (Finset.single_le_sum (fun i _ => hc i) hj).trans hQc
  have hQW : ∀ j ∈ Q, j ∉ W := by
    intro j hj hjW
    have := hQ hj
    rw [Finset.mem_sdiff] at this
    exact this.2 hjW
  have htgL : (PS v c B (l + 2)).tgt = 2 ^ (l + 2) * m :=
    (PS_t_tgt (c := c) hv hmono hB.le (k := l + 2) (by omega)).2
  -- structure of `W1`, `W̄2`
  have hW1 : (sF.prev.dropLast).toFinset ⊆ W ∧ sF.cur.toFinset ⊆ W := by
    have hpr : pruned v c B = prune v c B sF := rfl
    rcases prune_cases v c hB.le sF with ⟨_, he⟩ | ⟨_, j0, _, hcase⟩
    · have e1 : W1 v c B = sF.prev := by unfold W1; rw [hpr, he]
      have e2 : W2bar v c B = sF.cur := by unfold W2bar; rw [hpr, he]
      refine ⟨?_, ?_⟩
      · intro x hx; rw [hW, e1]; apply Finset.mem_union_left
        simp only [List.mem_toFinset] at hx ⊢; exact List.dropLast_subset _ hx
      · intro x hx; rw [hW, e2]; exact Finset.mem_union_right _ hx
    · simp only at hcase
      rcases hcase with ⟨_, he⟩ | ⟨_, he⟩
      · have e1 : W1 v c B = sF.prev.dropLast := by unfold W1; rw [hpr, he]
        have e2 : W2bar v c B = sF.cur ++ [j0] := by unfold W2bar; rw [hpr, he]
        refine ⟨?_, ?_⟩
        · intro x hx; rw [hW, e1]; exact Finset.mem_union_left _ hx
        · intro x hx; rw [hW, e2]; apply Finset.mem_union_right
          simp only [List.mem_toFinset, List.mem_append] at hx ⊢; exact Or.inl hx
      · have e1 : W1 v c B = sF.prev.dropLast := by unfold W1; rw [hpr, he]
        have e2 : W2bar v c B = sF.cur := by unfold W2bar; rw [hpr, he]
        refine ⟨?_, ?_⟩
        · intro x hx; rw [hW, e1]; exact Finset.mem_union_left _ hx
        · intro x hx; rw [hW, e2]; exact Finset.mem_union_right _ hx
  -- bidders still active at the end of the run
  have hactive : ∀ j ∈ Q, j ∈ sF.A →
      marg v {j} sF.cur.toFinset * B < c j * (2 ^ (l + 2) * m) := by
    intro j hj hjA
    have hjW := hQW j hj
    have hpr : pruned v c B = prune v c B sF := rfl
    rcases pool_empty_mem hpool hjA with hjp | hjc
    swap
    · exact absurd (hW1.2 (List.mem_toFinset.2 hjc)) hjW
    rcases prune_cases v c hB.le sF with ⟨_, he⟩ | ⟨_, j0, hj0, hcase⟩
    · exfalso
      have e1 : W1 v c B = sF.prev := by unfold W1; rw [hpr, he]
      apply hjW; rw [hW, e1]; exact Finset.mem_union_left _ (List.mem_toFinset.2 hjp)
    · have hjd : j ∉ sF.prev.dropLast := fun h => hjW (hW1.1 (List.mem_toFinset.2 h))
      have hjj0 := mem_of_not_mem_dropLast hj0 hjp hjd
      subst hjj0
      simp only at hcase
      rcases hcase with ⟨_, he⟩ | ⟨hrej, _⟩
      · exfalso
        have e2 : W2bar v c B = sF.cur ++ [j] := by unfold W2bar; rw [hpr, he]
        apply hjW; rw [hW, e2]; apply Finset.mem_union_right; simp
      · have htg' : sF.tgt = 2 ^ (l + 2) * m := by rw [hsFeq]; exact htgL
        have hτ : 0 < sF.tgt := by rw [htg']; positivity
        have key : marg v {j} sF.cur.toFinset * B / sF.tgt < c j := by
          rcases lt_or_ge (sF.p j) (marg v {j} sF.cur.toFinset * B / sF.tgt) with hlt | hge
          · rw [min_eq_left hlt.le] at hrej
            rcases gF.cost j hjA with h1 | h1
            · exact absurd h1 hrej
            · rw [h1] at hrej; linarith [hcB j hj]
          · rw [min_eq_right hge] at hrej; linarith
        rw [div_lt_iff₀ hτ, htg'] at key
        linarith
  -- the split of `Q`
  set Qa := Q.filter (fun j => j ∉ (PS v c B l).A) with hQa
  set Qb := Q.filter (fun j => j ∈ (PS v c B l).A) with hQb
  have hQab : Q = Qa ∪ Qb := by
    rw [hQa, hQb, Finset.union_comm]; exact (Finset.filter_union_filter_not_eq _ Q).symm
  -- bound on `Qb`
  have hQbB : ∀ j ∈ Qb, marg v {j} W * B ≤ c j * (2 ^ (l + 2) * m) := by
    intro j hj
    rw [hQb, Finset.mem_filter] at hj
    obtain ⟨hjQ, hjl⟩ := hj
    by_cases hjA : j ∈ sF.A
    · have h1 := hactive j hjQ hjA
      have h2 := marg_anti hmono hsub {j} hW1.2
      nlinarith
    · rw [hsFeq] at hjA
      obtain ⟨k', hk1, hkK, hkL, hjA1, hjA2⟩ := rej_phase (c := c) hmono hv hB.le (by omega) hjA
      have hkl : l + 1 ≤ k' := by
        by_contra hlt
        exact hjA2 (PS_A_mono (c := c) hmono hv hB.le (show k' ≤ l by omega) hjl)
      obtain ⟨i, hi, hv1, hm1⟩ := rej_record (c := c) hmono hv hB hm hk1 hkL hjA1 hjA2 (hcB j hjQ)
      rcases Nat.lt_or_ge k' (l + 2) with hk | hk
      · -- removed in phase `t̂ - 1`
        have hke : k' = l + 1 := by omega
        subst hke
        have hreach := phase_reached (c := c) hmono hv hB.le (k := l + 1) (by omega)
        rw [(PS_t_tgt (c := c) hv hmono hB.le (k := l + 1) (by omega)).2] at hreach
        have hi' : i < (PS v c B (l + 1)).cur.length := by
          rcases Nat.lt_or_ge i (PS v c B (l + 1)).cur.length with h | h
          · exact h
          · exfalso
            have : i = (PS v c B (l + 1)).cur.length := le_antisymm hi h
            rw [this, List.take_length] at hv1; linarith
        have hsubW : ((PS v c B (l + 1)).cur.take i).toFinset ⊆ W := by
          refine (take_sub_dropLast _ i hi').trans ?_
          rw [← hprev]; exact hW1.1
        have h2 := marg_anti hmono hsub {j} hsubW
        have hp : (2:ℝ) ^ (l + 1) * m ≤ 2 ^ (l + 2) * m := by
          have : (2:ℝ) ^ (l + 1) ≤ 2 ^ (l + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
          nlinarith
        have hcj := hc j
        nlinarith
      · -- removed in phase `t̂`
        have hke : k' = l + 2 := by omega
        subst hke
        have hsubW : ((PS v c B (l + 2)).cur.take i).toFinset ⊆ W := by
          refine (take_toFinset_sub _ i).trans ?_
          rw [← hsFeq]; exact hW1.2
        have h2 := marg_anti hmono hsub {j} hsubW
        nlinarith
  -- the union `𝐒` of the earlier phase sets
  set SS := (Finset.Icc 2 (l + 1)).biUnion (fun t => (PS v c B (t - 1)).cur.dropLast.toFinset)
    with hSS
  have hSSv : v SS - v ∅ ≤ (2 ^ (l + 1) - 2) * m := by
    refine (subadd_biUnion' hmono hsub _ _).trans ?_
    rw [← geom_sum (l + 1) (by omega), Finset.sum_mul]
    apply Finset.sum_le_sum
    intro t ht
    rw [Finset.mem_Icc] at ht
    have hI := (phase_facts (c := c) hv hmono hB.le (k := t - 2) (by omega)).1
    rw [show t - 2 + 1 = t - 1 by omega] at hI
    have htg := (PS_t_tgt (c := c) hv hmono hB.le (k := t - 1) (by omega)).2
    by_cases hne : (PS v c B (t - 1)).cur = []
    · rw [hne]; simp; positivity
    · have hb : v (PS v c B (t - 1)).cur.dropLast.toFinset < (PS v c B (t - 1)).tgt := by
        rw [List.dropLast_eq_take]
        exact hI.below _ (by have := List.length_pos_iff.2 hne; omega)
      rw [htg] at hb
      have := hv ∅
      linarith
  have hQaB : ∀ j ∈ Qa, marg v {j} SS * B ≤ c j * (2 ^ l * m) := by
    intro j hj
    rw [hQa, Finset.mem_filter] at hj
    obtain ⟨hjQ, hjl⟩ := hj
    obtain ⟨k', hk1, hkK, hkL, hjA1, hjA2⟩ := rej_phase (c := c) hmono hv hB.le (by omega) hjl
    obtain ⟨i, hi, hv1, hm1⟩ := rej_record (c := c) hmono hv hB hm hk1 hkL hjA1 hjA2 (hcB j hjQ)
    have hreach := phase_reached (c := c) hmono hv hB.le (k := k') (by omega)
    rw [(PS_t_tgt (c := c) hv hmono hB.le (k := k') (by omega)).2] at hreach
    have hi' : i < (PS v c B k').cur.length := by
      rcases Nat.lt_or_ge i (PS v c B k').cur.length with h | h
      · exact h
      · exfalso
        have : i = (PS v c B k').cur.length := le_antisymm hi h
        rw [this, List.take_length] at hv1; linarith
    have hsubS : ((PS v c B k').cur.take i).toFinset ⊆ SS := by
      refine (take_sub_dropLast _ i hi').trans ?_
      intro x hx
      rw [hSS, Finset.mem_biUnion]
      exact ⟨k' + 1, Finset.mem_Icc.2 ⟨by omega, by omega⟩, by simpa using hx⟩
    have h2 := marg_anti hmono hsub {j} hsubS
    have hp : (2:ℝ) ^ k' * m ≤ 2 ^ l * m := by
      have : (2:ℝ) ^ k' ≤ 2 ^ l := pow_le_pow_right₀ (by norm_num) (by omega)
      nlinarith
    have hcj := hc j
    nlinarith
  -- assembling
  have hA : marg v Qa W ≤ (∑ j ∈ Qa, c j) * (2 ^ l * m) / B + (2 ^ (l + 1) - 2) * m := by
    have h1 := marg_anti hmono hsub Qa (Finset.empty_subset W)
    have h2 : marg v Qa ∅ ≤ marg v Qa SS + (v SS - v ∅) := by
      unfold marg
      have := hmono (∅ ∪ Qa) (SS ∪ Qa) (Finset.union_subset_union (Finset.empty_subset _) le_rfl)
      linarith
    have h3 := marg_le_sum hmono hsub SS Qa
    have h4 : ∑ j ∈ Qa, marg v {j} SS ≤ (∑ j ∈ Qa, c j) * (2 ^ l * m) / B := by
      rw [le_div_iff₀ hB, Finset.sum_mul, Finset.sum_mul]
      exact Finset.sum_le_sum hQaB
    linarith
  have hBb : marg v Qb W ≤ (∑ j ∈ Qb, c j) * (2 ^ (l + 2) * m) / B := by
    have h3 := marg_le_sum hmono hsub W Qb
    have h4 : ∑ j ∈ Qb, marg v {j} W ≤ (∑ j ∈ Qb, c j) * (2 ^ (l + 2) * m) / B := by
      rw [le_div_iff₀ hB, Finset.sum_mul, Finset.sum_mul]
      exact Finset.sum_le_sum hQbB
    linarith
  have hsplit := marg_union_le hmono hsub W Qa Qb
  rw [← hQab] at hsplit
  have hsumc : ∑ j ∈ Qa, c j + ∑ j ∈ Qb, c j ≤ B := by
    rw [← Finset.sum_union (Finset.disjoint_filter_filter_not Q Q _).symm, ← hQab]
    · exact hQc
  have hca : 0 ≤ ∑ j ∈ Qa, c j := Finset.sum_nonneg (fun i _ => hc i)
  have hcb : 0 ≤ ∑ j ∈ Qb, c j := Finset.sum_nonneg (fun i _ => hc i)
  rw [htarget, hl, show l + 3 - 2 = l + 1 by omega, show l + 3 - 1 = l + 2 by omega]
  -- final arithmetic
  set a : ℝ := 2 ^ l with ha
  have ha0 : 0 < a := by positivity
  have e1 : (2:ℝ) ^ (l + 1) = 2 * a := by rw [ha, pow_succ]; ring
  have e2 : (2:ℝ) ^ (l + 2) = 4 * a := by rw [ha, pow_succ, pow_succ]; ring
  rw [e1] at hA
  rw [e2] at hBb
  rw [e1, e2]
  have hfa : (∑ j ∈ Qa, c j) * (a * m) / B ≤ (∑ j ∈ Qa, c j) * (4 * a * m) / B := by
    apply div_le_div_of_nonneg_right _ hB.le
    have : 0 ≤ (∑ j ∈ Qa, c j) * (a * m) := by positivity
    nlinarith
  have hsum2 : (∑ j ∈ Qa, c j) * (4 * a * m) / B + (∑ j ∈ Qb, c j) * (4 * a * m) / B ≤
      4 * a * m := by
    rw [← add_div, ← add_mul, div_le_iff₀ hB]
    have : 0 ≤ 4 * a * m := by positivity
    nlinarith
  have hfin : (3 / 2 - 1 / (2 * a)) * (4 * a * m) = 6 * a * m - 2 * m := by
    field_simp; ring
  rw [hfin]
  linarith

end BCMCore

namespace BCMCore
open BudgetClock.Monotone

variable {n : ℕ}

theorem listCost_const (a : ℝ) (L : List (Fin n)) : listCost (fun _ => a) L = L.length * a := by
  unfold listCost
  induction L with
  | nil => simp
  | cons x L ih => simp [List.map_cons, List.sum_cons]; ring

/-- If every marginal along `L` is at least `a`, then `|L| a ≤ v(L) − v(∅)`. -/
theorem tele_ge {v : Finset (Fin n) → ℝ} (a : ℝ) (L : List (Fin n))
    (h : ∀ k (hk : k < L.length), a ≤ marg v {L[k]} (L.take k).toFinset) :
    L.length * a ≤ v L.toFinset - v ∅ := by
  have := cost_le_of_marg (v := v) (p := fun _ => a) (τ := 1) (B := 1) L
    (by intro k hk; simpa using h k hk)
  rw [listCost_const] at this
  linarith

/-- If every marginal along `L` is at most `a`, then `v(L) − v(∅) ≤ |L| a`. -/
theorem tele_le {v : Finset (Fin n) → ℝ} (a : ℝ) (L : List (Fin n))
    (h : ∀ k (hk : k < L.length), marg v {L[k]} (L.take k).toFinset ≤ a) :
    v L.toFinset - v ∅ ≤ L.length * a := by
  have := cost_ge_of_marg (v := v) (p := fun _ => a) (τ := 1) (B := 1) L
    (by intro k hk; simpa using h k hk)
  rw [listCost_const] at this
  linarith

theorem val_dropLast {v : Finset (Fin n) → ℝ} (L : List (Fin n)) (hL : L ≠ []) :
    v L.toFinset = v L.dropLast.toFinset +
      marg v {L[L.length - 1]'(by have := List.length_pos_iff.2 hL; omega)} L.dropLast.toFinset := by
  unfold marg
  have e : L.toFinset = L.dropLast.toFinset ∪ {L[L.length - 1]'(by
      have := List.length_pos_iff.2 hL; omega)} := by
    conv_lhs => rw [← List.dropLast_append_getLast hL]
    rw [List.getLast_eq_getElem]
    simp only [List.toFinset_append, List.toFinset_cons, List.toFinset_nil, insert_empty_eq]
  rw [e]; ring

/-- **Lemma 3**. -/
theorem lemma3_core {v : Finset (Fin n) → ℝ} (hv : ∀ S, 0 ≤ v S) (hmono : IsMonotone v)
    (hsub : NonmonotoneSubmod.Shared.Submodular v) (c : Fin n → ℝ)
    (B : ℝ) (hB : 0 < B) (t : ℕ) (ht2 : 2 ≤ t) (htle : t ≤ lastPhase v c B)
    (hinf : B < listCost (phasePrices v c B t) (phaseSet v c B t)) :
    ((2 : ℝ) ^ (t - 1) / ((2 : ℝ) ^ (t - 1) + 1)) * target v c B t ≤
      v (phaseSet v c B t).dropLast.toFinset := by
  obtain ⟨k, rfl⟩ : ∃ k, t = k + 2 := ⟨t - 2, by omega⟩
  unfold phasePrices phaseSet target at *
  rw [phaseState_eq, show k + 2 - 1 = k + 1 by omega] at *
  obtain ⟨hI, _⟩ := phase_facts (c := c) hv hmono hB.le (k := k) htle
  set s := PS v c B (k + 1) with hs
  have hne : s.cur ≠ [] := by
    intro h; rw [h] at hinf; simp [listCost] at hinf; linarith
  have hτ := hI.tgt_pos hv hne
  have htg : s.tgt = 2 ^ (k + 1) * mval v B :=
    (PS_t_tgt (c := c) hv hmono hB.le (k := k + 1) (by omega)).2
  have hm : 0 < mval v B := by
    rw [htg] at hτ; exact pos_of_mul_pos_right hτ (by positivity)
  -- value exceeds the target
  have hcost := cost_le_of_marg (v := v) (p := s.p) (τ := s.tgt) (B := B) s.cur
    (fun j hj => hI.price_le hτ j hj)
  have hval : s.tgt < v s.cur.toFinset - v ∅ := by
    by_contra hc; push Not at hc
    have : B * s.tgt < listCost s.p s.cur * s.tgt := mul_lt_mul_of_pos_right hinf hτ
    nlinarith
  set K := s.cur.length with hK
  have hK1 : 1 ≤ K := List.length_pos_iff.2 hne
  -- the number of bidders
  have hup := tele_le (v := v) (mval v B) s.cur
    (fun j hj => marg_single_le hv hsub _ (single_le_mval v B) _ _)
  have hKbig : 2 ^ (k + 1) + 1 ≤ K := by
    have h1 : (2:ℝ) ^ (k + 1) * mval v B < K * mval v B := by rw [← htg]; linarith
    have h2 : (2:ℝ) ^ (k + 1) < K := lt_of_mul_lt_mul_right h1 hm.le
    have h3 : 2 ^ (k + 1) < K := by exact_mod_cast h2
    omega
  -- the last marginal is the smallest
  set δ := marg v {s.cur[K - 1]'(by omega)} (s.cur.take (K - 1)).toFinset with hδ
  have hD : s.cur.dropLast = s.cur.take (K - 1) := List.dropLast_eq_take
  have hlow := tele_ge (v := v) δ s.cur.dropLast (by
    intro j hj
    have hjK : j < K - 1 := by simp at hj; omega
    rw [dropLast_getElem _ j hj, dropLast_take _ j hj]
    have g := hI.greedy2 j (K - 1) (by omega) hjK
    have a := marg_anti hmono hsub {s.cur[K - 1]'(by omega)}
      (show (s.cur.take j).toFinset ⊆ (s.cur.take (K - 1)).toFinset by
        intro x hx
        simp only [List.mem_toFinset] at hx ⊢
        have : s.cur.take j = (s.cur.take (K - 1)).take j := by
          rw [List.take_take]; congr 1; omega
        rw [this] at hx; exact List.mem_of_mem_take hx)
    linarith)
  have hsplit := val_dropLast (v := v) s.cur hne
  rw [hD] at hsplit hlow
  have hDlen : (s.cur.take (K - 1)).length = K - 1 := by simp; omega
  rw [hDlen] at hlow
  rw [← hδ] at hsplit
  have hv0 := hv ∅
  -- K v(D) ≥ (K - 1) v(S) ≥ (K - 1) τ
  have hKr : ((K - 1 : ℕ) : ℝ) = (K : ℝ) - 1 := by
    rw [Nat.cast_sub hK1]; simp
  rw [hKr] at hlow
  have hKa : ((2:ℝ) ^ (k + 1) + 1) ≤ K := by exact_mod_cast hKbig
  rw [hD]
  set a : ℝ := (2:ℝ) ^ (k + 1) with ha
  have ha0 : 0 < a := by positivity
  set D := v (s.cur.take (K - 1)).toFinset with hDdef
  have hSv : v s.cur.toFinset = D + δ := hsplit
  -- K D ≥ (K-1)(D + δ) = (K-1) v(S)
  have h1 : (K : ℝ) * D ≥ ((K : ℝ) - 1) * v s.cur.toFinset := by
    rw [hSv]; nlinarith
  have h2 : ((K : ℝ) - 1) * v s.cur.toFinset ≥ ((K : ℝ) - 1) * s.tgt := by
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    linarith
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  have hKpos : (0:ℝ) < K := by linarith
  -- a τ K ≤ (K - 1)(a + 1) τ ≤ D K (a + 1)
  have h3 : a * s.tgt * K ≤ ((K : ℝ) - 1) * (a + 1) * s.tgt := by
    have : a * K ≤ ((K : ℝ) - 1) * (a + 1) := by nlinarith
    nlinarith
  have h4 : ((K : ℝ) - 1) * (a + 1) * s.tgt ≤ D * (a + 1) * K := by nlinarith
  have h5 : a * s.tgt * K ≤ D * (a + 1) * K := le_trans h3 h4
  have := le_of_mul_le_mul_right h5 hKpos
  linarith

end BCMCore

namespace BCMCore
open BudgetClock.Monotone

variable {n : ℕ}

theorem getLast_not_mem_dropLast {α : Type} {l : List α} {a : α} (hnd : l.Nodup)
    (hl : l.getLast? = some a) : a ∉ l.dropLast := by
  have hne : l ≠ [] := by intro h; rw [h] at hl; simp at hl
  have e := List.dropLast_append_getLast hne
  rw [List.getLast?_eq_some_getLast hne, Option.some.injEq] at hl
  rw [← e] at hnd
  rw [List.nodup_append] at hnd
  intro ha
  exact hnd.2.2 a ha (l.getLast hne) (by simp) (by rw [hl])

theorem final_p_nonneg {v : Finset (Fin n) → ℝ} {c : Fin n → ℝ} {B : ℝ} (hv : ∀ S, 0 ≤ v S)
    (hmono : IsMonotone v) (hB : 0 ≤ B) : ∀ i, 0 ≤ finalPrices v c B i := by
  have g := GInv.all (c := c) hv hmono hB (n + 2)
  rw [← finalState_eq] at g
  have htgt : 0 ≤ (finalState v c B).tgt := by
    rw [g.tgt]; exact mul_nonneg (by positivity) (mval_nonneg hv B)
  intro i
  unfold finalPrices pruned
  rcases prune_cases v c hB (finalState v c B) with ⟨_, he⟩ | ⟨_, j0, _, hcase⟩
  · rw [he]; exact g.p_nn i
  · simp only at hcase
    have hx : 0 ≤ min ((finalState v c B).p j0)
        (marg v {j0} (finalState v c B).cur.toFinset * B / (finalState v c B).tgt) :=
      le_min (g.p_nn j0) (div_nonneg (mul_nonneg (marg_nonneg hmono _ _) hB) htgt)
    rcases hcase with ⟨_, he⟩ | ⟨_, he⟩
    all_goals
      rw [he]
      by_cases hij : i = j0
      · subst hij; simp only [Function.update_self]; exact hx
      · simp only [Function.update_of_ne hij]; exact g.p_nn i

/-- `W1` costs at most `B` at the final prices. -/
theorem W1_cost {v : Finset (Fin n) → ℝ} {c : Fin n → ℝ} {B : ℝ} (hv : ∀ S, 0 ≤ v S)
    (hmono : IsMonotone v) (hB : 0 ≤ B) : listCost (finalPrices v c B) (W1 v c B) ≤ B := by
  have g := GInv.all (c := c) hv hmono hB (n + 2)
  rw [← finalState_eq] at g
  unfold finalPrices W1 pruned
  rcases prune_cases v c hB (finalState v c B) with ⟨hb, he⟩ | ⟨hb, j0, hj0, hcase⟩
  · rw [he]; exact le_of_not_gt hb
  · simp only at hcase
    have hnot := getLast_not_mem_dropLast g.prev_nodup hj0
    have key : listCost (finalState v c B).p (finalState v c B).prev.dropLast ≤ B := by
      have hL := lastPhase_ge v c B
      rcases Nat.lt_or_ge (lastPhase v c B) 2 with h1 | h2
      · exfalso
        have e : finalState v c B = PS v c B 0 := by
          rw [final_eq, show lastPhase v c B - 1 = 0 by omega]
        rw [e] at hb; simp [PS_zero, initState, listCost] at hb; linarith
      · obtain ⟨hprev, hprevp⟩ := final_prev (c := c) hv hmono hB h2
        rw [listCost_congr (fun i hi => hprevp i (List.dropLast_subset _ hi)), hprev]
        rcases Nat.lt_or_ge (lastPhase v c B) 3 with h3 | h3
        · rw [show lastPhase v c B - 2 = 0 by omega, PS_zero]
          unfold initState; simp only
          split_ifs <;> simp [listCost] <;> exact hB
        · obtain ⟨hI, _⟩ := phase_facts (c := c) hv hmono hB (k := lastPhase v c B - 3) (by omega)
          rw [show lastPhase v c B - 3 + 1 = lastPhase v c B - 2 by omega] at hI
          exact hI.cost_dropLast hv hB
    rcases hcase with ⟨_, he⟩ | ⟨_, he⟩
    all_goals
      rw [he]
      simp only
      rw [listCost_congr (fun i hi => Function.update_of_ne (fun (h : i = j0) => hnot (by rw [← h]; exact hi)) _ _)]
      exact key

theorem W2_cost {v : Finset (Fin n) → ℝ} {c : Fin n → ℝ} {B : ℝ} (hB : 0 ≤ B) :
    listCost (finalPrices v c B) (W2 v c B) ≤ B := by
  unfold W2 mvW2 longestFeasiblePrefix
  exact Nat.findGreatest_spec (P := fun k => listCost (finalPrices v c B)
    ((W2bar v c B).take k) ≤ B) (Nat.zero_le _) (by simp [listCost]; exact hB)

theorem listCost_append (p : Fin n → ℝ) (L1 L2 : List (Fin n)) :
    listCost p (L1 ++ L2) = listCost p L1 + listCost p L2 := by
  simp [listCost]

theorem W3_cost {v : Finset (Fin n) → ℝ} {c : Fin n → ℝ} {B : ℝ} (hB : 0 ≤ B) :
    listCost (finalPrices v c B) (W3 v c B) ≤ B := by
  unfold W3 Tpre mvT
  rw [listCost_append]
  exact Nat.findGreatest_spec (P := fun k => listCost (finalPrices v c B) (W2 v c B) +
    listCost (finalPrices v c B) ((W1 v c B).take k) ≤ B) (Nat.zero_le _)
    (by simp [listCost]; exact W2_cost hB)

theorem iterativePruning_eq (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (B : ℝ) :
    iterativePruning v c B =
      (if v (W3 v c B).toFinset ≤ v (W1 v c B).toFinset then (W1 v c B).toFinset
        else (W3 v c B).toFinset, finalPrices v c B) := rfl

/-- **Lemma 11**. -/
theorem lemma11_core {v : Finset (Fin n) → ℝ} (hv : ∀ S, 0 ≤ v S) (hmono : IsMonotone v)
    (c : Fin n → ℝ) (B : ℝ) (hB : 0 < B) :
    listCost (finalPrices v c B) (W1 v c B) ≤ B ∧
    listCost (finalPrices v c B) (W2 v c B) ≤ B ∧
    listCost (finalPrices v c B) (W3 v c B) ≤ B ∧
    ∑ i ∈ (iterativePruning v c B).1, (iterativePruning v c B).2 i ≤ B := by
  have h1 := W1_cost (c := c) hv hmono hB.le
  have h3 := W3_cost (v := v) (c := c) hB.le
  refine ⟨h1, W2_cost hB.le, h3, ?_⟩
  have hp := final_p_nonneg (c := c) hv hmono hB.le
  rw [iterativePruning_eq]
  simp only
  split_ifs
  · exact (sum_toFinset_le _ (fun i _ => hp i)).trans h1
  · exact (sum_toFinset_le _ (fun i _ => hp i)).trans h3

end BCMCore

namespace BCMCore
open BudgetClock.Monotone

variable {n : ℕ}

/-- §3, p. 7: the benchmark. -/
theorem benchmark_core {v : Finset (Fin n) → ℝ} (hmono : IsMonotone v) (c : Fin n → ℝ)
    (hc : ∀ i, 0 ≤ c i) (B : ℝ) (W : Finset (Fin n)) :
    ∀ O : Finset (Fin n), ∑ i ∈ O, c i ≤ B →
      ∃ Q : Finset (Fin n), Q ⊆ Finset.univ \ W ∧ ∑ i ∈ Q, c i ≤ B ∧
        v O ≤ v W + marg v Q W := by
  intro O hO
  refine ⟨O \ W, ?_, ?_, ?_⟩
  · intro x hx
    rw [Finset.mem_sdiff] at hx ⊢
    exact ⟨Finset.mem_univ _, hx.2⟩
  · refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
      (fun i _ _ => hc i)) hO
  · unfold marg
    rw [Finset.union_sdiff_self_eq_union]
    have := hmono O (W ∪ O) Finset.subset_union_right
    linarith

/-- Shape of `W1`: a prefix of `S_{t̂-1}` (all of it, or all but the last bidder) on which the final
prices agree with the prices at the end of phase `t̂ - 1`. -/
theorem W1_shape {v : Finset (Fin n) → ℝ} {c : Fin n → ℝ} {B : ℝ} (hv : ∀ S, 0 ≤ v S)
    (hmono : IsMonotone v) (hB : 0 ≤ B) (hL : 2 ≤ lastPhase v c B) :
    ∃ r, W1 v c B = (PS v c B (lastPhase v c B - 2)).cur.take r ∧
      (r = (PS v c B (lastPhase v c B - 2)).cur.length ∨
        r + 1 = (PS v c B (lastPhase v c B - 2)).cur.length) ∧
      ∀ i ∈ W1 v c B, finalPrices v c B i = (PS v c B (lastPhase v c B - 2)).p i := by
  have g := GInv.all (c := c) hv hmono hB (n + 2)
  rw [← finalState_eq] at g
  obtain ⟨hprev, hprevp⟩ := final_prev (c := c) hv hmono hB hL
  unfold finalPrices W1 pruned
  rcases prune_cases v c hB (finalState v c B) with ⟨_, he⟩ | ⟨hb, j0, hj0, hcase⟩
  · rw [he]
    refine ⟨(PS v c B (lastPhase v c B - 2)).cur.length, ?_, Or.inl rfl, ?_⟩
    · simp only; rw [hprev, List.take_length]
    · intro i hi; exact hprevp i hi
  · simp only at hcase
    have hnot := getLast_not_mem_dropLast g.prev_nodup hj0
    have hne : (finalState v c B).prev ≠ [] := by
      intro h; rw [h] at hb; simp [listCost] at hb; linarith
    rw [hprev] at hne
    have hlen := List.length_pos_iff.2 hne
    rcases hcase with ⟨_, he⟩ | ⟨_, he⟩
    all_goals
      rw [he]
      refine ⟨(PS v c B (lastPhase v c B - 2)).cur.length - 1, ?_, Or.inr (by omega), ?_⟩
      · simp only; rw [hprev, List.dropLast_eq_take]
      · intro i hi
        simp only at hi ⊢
        have hij : i ≠ j0 := fun h => hnot (by rw [← h]; exact hi)
        rw [Function.update_of_ne hij]
        exact hprevp i (List.dropLast_subset _ hi)

/-- Appendix A.1, p. 20: the value of the prefix `T`. -/
theorem prefixT_core {v : Finset (Fin n) → ℝ} (hv : ∀ S, 0 ≤ v S) (hmono : IsMonotone v)
    (hsub : NonmonotoneSubmod.Shared.Submodular v) (c : Fin n → ℝ)
    (B : ℝ) (hB : 0 < B) (h3 : 3 ≤ lastPhase v c B) :
    (1 - listCost (finalPrices v c B) (W2 v c B) / B - 1 / (2 : ℝ) ^ (lastPhase v c B - 2)) *
        target v c B (lastPhase v c B) / 2 ≤ v (Tpre v c B).toFinset := by
  have htarget : target v c B (lastPhase v c B) = 2 ^ (lastPhase v c B - 1) * mval v B := by
    unfold target; rw [phaseState_eq]
    exact (PS_t_tgt (c := c) hv hmono hB.le (k := lastPhase v c B - 1) (by omega)).2
  rcases (mval_nonneg hv B).lt_or_eq with hm | hm
  swap
  · have h0 := v_zero_of_mval_zero hv hmono hsub hm.symm
    rw [htarget, ← hm, h0]; simp
  obtain ⟨l, hl⟩ : ∃ l, lastPhase v c B = l + 3 := ⟨lastPhase v c B - 3, by omega⟩
  obtain ⟨r, hW1, hr, hpW1⟩ := W1_shape (c := c) hv hmono hB.le (by omega)
  rw [hl, show l + 3 - 2 = l + 1 by omega] at hW1 hr hpW1
  rw [htarget, hl, show l + 3 - 2 = l + 1 by omega, show l + 3 - 1 = l + 2 by omega]
  set S := (PS v c B (l + 1)).cur with hS
  set pS := (PS v c B (l + 1)).p with hpS
  set m := mval v B with hmdef
  obtain ⟨hI, _⟩ := phase_facts (c := c) hv hmono hB.le (k := l) (by omega)
  have htg' : (PS v c B (l + 1)).tgt = 2 ^ (l + 1) * m :=
    (PS_t_tgt (c := c) hv hmono hB.le (k := l + 1) (by omega)).2
  have hreach := phase_reached (c := c) hmono hv hB.le (k := l + 1) (by omega)
  rw [htg'] at hreach
  have hτ : 0 < (PS v c B (l + 1)).tgt := by rw [htg']; positivity
  set p' := finalPrices v c B with hp'
  set c2 := listCost p' (W2 v c B) with hc2
  have hc2nn : 0 ≤ c2 := listCost_nonneg (fun i _ => final_p_nonneg (c := c) hv hmono hB.le i)
  have hm1 := single_le_mval v B
  -- v(W1) ≥ v(S) − m
  have hvW1 : v S.toFinset - m ≤ v (W1 v c B).toFinset := by
    rcases hr with hr | hr
    · have e : W1 v c B = S := by simp [hW1, hr]
      rw [e]; linarith
    · have hne : S ≠ [] := by intro h; rw [h] at hr; simp at hr
      have hsplit := val_dropLast (v := v) S hne
      have hle := marg_single_le hv hsub m hm1 (S[S.length - 1]'(by
        have := List.length_pos_iff.2 hne; omega)) S.dropLast.toFinset
      rw [hW1, show r = S.length - 1 by omega, ← List.dropLast_eq_take]
      linarith
  -- the prefix `T`
  set P : ℕ → Prop := fun k => listCost p' (W2 v c B) + listCost p' ((W1 v c B).take k) ≤ B
    with hP
  have hT : Tpre v c B = (W1 v c B).take (Nat.findGreatest P (W1 v c B).length) := rfl
  set ks := Nat.findGreatest P (W1 v c B).length with hks
  have hks_le : ks ≤ (W1 v c B).length := Nat.findGreatest_le _
  have e2 : (2:ℝ) ^ (l + 2) = 2 * 2 ^ (l + 1) := by rw [pow_succ]; ring
  have hlhs : (1 - c2 / B - 1 / (2:ℝ) ^ (l + 1)) * (2 ^ (l + 2) * m) / 2 =
      (1 - c2 / B) * (2 ^ (l + 1) * m) - m := by
    rw [e2]; field_simp
  rw [hlhs]
  have hcB : 0 ≤ c2 / B := div_nonneg hc2nn hB.le
  have hτ0 : 0 ≤ (2:ℝ) ^ (l + 1) * m := by positivity
  rcases Nat.lt_or_ge ks (W1 v c B).length with hlt | hge
  · -- `T` is a proper prefix: the next bidder overflows the budget
    have hnot : ¬ P (ks + 1) := Nat.findGreatest_is_greatest (Nat.lt_succ_self _) (by omega)
    simp only [hP, not_le] at hnot
    have hrk : ks + 1 ≤ r := by
      have : (W1 v c B).length = r := by
        rw [hW1, List.length_take]; rcases hr with hr | hr <;> omega
      omega
    have hT' : (W1 v c B).take (ks + 1) = S.take (ks + 1) := by
      rw [hW1, List.take_take]; congr 1; omega
    have hlenT' : (S.take (ks + 1)).length = ks + 1 := by
      rw [List.length_take]
      have : r ≤ S.length := by rcases hr with hr | hr <;> omega
      omega
    -- cost along `T'` at prices `pS`
    have hcostT := cost_le_of_marg (v := v) (p := pS) (τ := (PS v c B (l + 1)).tgt) (B := B)
      (S.take (ks + 1)) (by
        intro j hj
        have hj1 : j < ks + 1 := lt_of_lt_of_le hj (by rw [List.length_take]; exact min_le_left _ _)
        have hj2 : j < S.length := lt_of_lt_of_le hj (by rw [List.length_take]; exact min_le_right _ _)
        rw [List.getElem_take, List.take_take, show min j (ks + 1) = j by omega]
        exact hI.price_le hτ j hj2)
    have hcongr : listCost p' (S.take (ks + 1)) = listCost pS (S.take (ks + 1)) := by
      apply listCost_congr
      intro i hi
      rw [← hT'] at hi
      exact hpW1 i (List.mem_of_mem_take hi)
    rw [hT', hcongr] at hnot
    -- v(T') > (1 − c2/B) τ'
    have hvT' : (1 - c2 / B) * (2 ^ (l + 1) * m) ≤ v (S.take (ks + 1)).toFinset := by
      rw [htg'] at hcostT
      have hv0 := hv ∅
      have h1 : (B - c2) * (2 ^ (l + 1) * m) ≤ listCost pS (S.take (ks + 1)) * (2 ^ (l + 1) * m) :=
        mul_le_mul_of_nonneg_right (by linarith) hτ0
      have h2 : (1 - c2 / B) * (2 ^ (l + 1) * m) = (B - c2) * (2 ^ (l + 1) * m) / B := by
        field_simp
      rw [h2, div_le_iff₀ hB]
      nlinarith
    -- v(T) ≥ v(T') − m
    have hksS : ks < S.length := by
      have : r ≤ S.length := by rcases hr with hr | hr <;> omega
      omega
    have hsucc : (S.take (ks + 1)).toFinset ⊆ (Tpre v c B).toFinset ∪ {S[ks]'hksS} := by
      have e1 : S.take (ks + 1) = S.take ks ++ [S[ks]'hksS] :=
        List.take_succ_eq_append_getElem hksS
      have e2 : Tpre v c B = S.take ks := by
        rw [hT, hW1, List.take_take, show min ks r = ks by omega]
      rw [e1, e2]
      intro x hx
      simp only [List.toFinset_append, List.toFinset_cons, List.toFinset_nil,
        insert_empty_eq] at hx
      exact hx
    have hsa := subadd hv hsub (Tpre v c B).toFinset {S[ks]'hksS}
    have hmo := hmono _ _ hsucc
    have := hm1 (S[ks]'hksS)
    linarith
  · -- `T = W1`
    have hTW : Tpre v c B = W1 v c B := by
      rw [hT, show ks = (W1 v c B).length by omega, List.take_length]
    rw [hTW]
    have : c2 / B * (2 ^ (l + 1) * m) ≥ 0 := by positivity
    nlinarith

end BCMCore

namespace BCMCore
open BudgetClock.Monotone

variable {n : ℕ}

/-- Strong form of Lemma 3: `K v(D) ≥ (K - 1) v(S)`, `K ≥ 2^{t-1} + 1`, `τ ≤ v(S)`. -/
theorem lemma3_aux {v : Finset (Fin n) → ℝ} (hv : ∀ S, 0 ≤ v S) (hmono : IsMonotone v)
    (hsub : NonmonotoneSubmod.Shared.Submodular v) (c : Fin n → ℝ)
    (B : ℝ) (hB : 0 < B) (k : ℕ) (htle : k + 2 ≤ lastPhase v c B)
    (hinf : B < listCost (PS v c B (k + 1)).p (PS v c B (k + 1)).cur) :
    ∃ K : ℕ, 2 ^ (k + 1) + 1 ≤ K ∧
      (K : ℝ) * v (PS v c B (k + 1)).cur.dropLast.toFinset ≥
        ((K : ℝ) - 1) * v (PS v c B (k + 1)).cur.toFinset ∧
      (PS v c B (k + 1)).tgt ≤ v (PS v c B (k + 1)).cur.toFinset := by
  obtain ⟨hI, _⟩ := phase_facts (c := c) hv hmono hB.le (k := k) htle
  set s := PS v c B (k + 1) with hs
  have hne : s.cur ≠ [] := by
    intro h; rw [h] at hinf; simp [listCost] at hinf; linarith
  have hτ := hI.tgt_pos hv hne
  have htg : s.tgt = 2 ^ (k + 1) * mval v B :=
    (PS_t_tgt (c := c) hv hmono hB.le (k := k + 1) (by omega)).2
  have hm : 0 < mval v B := by
    rw [htg] at hτ; exact pos_of_mul_pos_right hτ (by positivity)
  have hcost := cost_le_of_marg (v := v) (p := s.p) (τ := s.tgt) (B := B) s.cur
    (fun j hj => hI.price_le hτ j hj)
  have hval : s.tgt < v s.cur.toFinset - v ∅ := by
    by_contra hc; push Not at hc
    have : B * s.tgt < listCost s.p s.cur * s.tgt := mul_lt_mul_of_pos_right hinf hτ
    nlinarith
  set K := s.cur.length with hK
  have hK1 : 1 ≤ K := List.length_pos_iff.2 hne
  have hup := tele_le (v := v) (mval v B) s.cur
    (fun j hj => marg_single_le hv hsub _ (single_le_mval v B) _ _)
  have hKbig : 2 ^ (k + 1) + 1 ≤ K := by
    have h1 : (2:ℝ) ^ (k + 1) * mval v B < K * mval v B := by rw [← htg]; linarith
    have h2 : (2:ℝ) ^ (k + 1) < K := lt_of_mul_lt_mul_right h1 hm.le
    have h3 : 2 ^ (k + 1) < K := by exact_mod_cast h2
    omega
  set δ := marg v {s.cur[K - 1]'(by omega)} (s.cur.take (K - 1)).toFinset with hδ
  have hD : s.cur.dropLast = s.cur.take (K - 1) := List.dropLast_eq_take
  have hlow := tele_ge (v := v) δ s.cur.dropLast (by
    intro j hj
    have hjK : j < K - 1 := by simp at hj; omega
    rw [dropLast_getElem _ j hj, dropLast_take _ j hj]
    have g := hI.greedy2 j (K - 1) (by omega) hjK
    have a := marg_anti hmono hsub {s.cur[K - 1]'(by omega)}
      (show (s.cur.take j).toFinset ⊆ (s.cur.take (K - 1)).toFinset by
        intro x hx
        simp only [List.mem_toFinset] at hx ⊢
        have : s.cur.take j = (s.cur.take (K - 1)).take j := by
          rw [List.take_take]; congr 1; omega
        rw [this] at hx; exact List.mem_of_mem_take hx)
    linarith)
  have hsplit := val_dropLast (v := v) s.cur hne
  rw [hD] at hsplit hlow
  have hDlen : (s.cur.take (K - 1)).length = K - 1 := by simp; omega
  rw [hDlen] at hlow
  rw [← hδ] at hsplit
  have hv0 := hv ∅
  have hKr : ((K - 1 : ℕ) : ℝ) = (K : ℝ) - 1 := by
    rw [Nat.cast_sub hK1]; simp
  rw [hKr] at hlow
  refine ⟨K, hKbig, ?_, by linarith⟩
  rw [hD, hsplit]
  nlinarith

theorem lfp_eq {p : Fin n → ℝ} {B : ℝ} (U : List (Fin n)) (hp : ∀ i ∈ U, 0 ≤ p i) (k : ℕ)
    (hk : k < U.length) (h1 : listCost p (U.take k) ≤ B) (h2 : B < listCost p (U.take (k + 1))) :
    longestFeasiblePrefix p B U = U.take k := by
  unfold longestFeasiblePrefix
  congr 1
  rw [Nat.findGreatest_eq_iff]
  refine ⟨hk.le, fun _ => h1, ?_⟩
  intro j hj hjU hP
  have hsub : (U.take (k + 1)).Sublist (U.take j) := List.take_sublist_take_left (by omega)
  have := listCost_sublist_le hsub (fun i hi => hp i (List.mem_of_mem_take hi))
  linarith

theorem W_ge (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (B : ℝ) :
    v (W1 v c B).toFinset ≤ v (iterativePruning v c B).1 ∧
      v (W3 v c B).toFinset ≤ v (iterativePruning v c B).1 := by
  rw [iterativePruning_eq]
  simp only
  split_ifs with h
  · exact ⟨le_rfl, h⟩
  · exact ⟨(lt_of_not_ge h).le, le_rfl⟩

theorem W2_le_W3 {v : Finset (Fin n) → ℝ} (hmono : IsMonotone v) (c : Fin n → ℝ) (B : ℝ) :
    v (W2 v c B).toFinset ≤ v (W3 v c B).toFinset := by
  apply hmono
  intro x hx
  unfold W3
  simp only [List.mem_toFinset, List.mem_append] at hx ⊢
  exact Or.inl hx

/-- For `t̂ = 2` there is no pruning. -/
theorem no_prune_L2 {v : Finset (Fin n) → ℝ} {c : Fin n → ℝ} {B : ℝ} (hv : ∀ S, 0 ≤ v S)
    (hmono : IsMonotone v) (hB : 0 ≤ B) (hL : lastPhase v c B = 2) :
    pruned v c B = ((finalState v c B).prev, (finalState v c B).cur, (finalState v c B).p) := by
  unfold pruned
  rcases prune_cases v c hB (finalState v c B) with ⟨_, he⟩ | ⟨hb, _, _, _⟩
  · exact he
  · exfalso
    obtain ⟨hprev, hprevp⟩ := final_prev (c := c) hv hmono hB (by omega)
    rw [listCost_congr hprevp, hprev, hL, show 2 - 2 = 0 by rfl, PS_zero] at hb
    unfold initState at hb; simp only at hb
    split_ifs at hb <;> simp [listCost] at hb <;> linarith

/-- The loss bound for `t̂ = 2`: `v(Q | W_1 ∪ W̄_2) ≤ OP̃T_2`. -/
theorem beta_L2 {v : Finset (Fin n) → ℝ} (hv : ∀ S, 0 ≤ v S) (hmono : IsMonotone v)
    (hsub : NonmonotoneSubmod.Shared.Submodular v) (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i)
    (B : ℝ) (hB : 0 < B) (hL : lastPhase v c B = 2) (hm : 0 < mval v B) :
    ∀ Q : Finset (Fin n),
      Q ⊆ Finset.univ \ ((W1 v c B).toFinset ∪ (W2bar v c B).toFinset) →
      ∑ i ∈ Q, c i ≤ B →
      marg v Q ((W1 v c B).toFinset ∪ (W2bar v c B).toFinset) ≤ 2 * mval v B := by
  intro Q hQ hQc
  have hnp := no_prune_L2 (c := c) hv hmono hB.le hL
  have e1 : W1 v c B = (finalState v c B).prev := by unfold W1; rw [hnp]
  have e2 : W2bar v c B = (finalState v c B).cur := by unfold W2bar; rw [hnp]
  set W := (W1 v c B).toFinset ∪ (W2bar v c B).toFinset with hW
  have hsF : finalState v c B = PS v c B 1 := by rw [final_eq, hL]
  have hpool := final_pool_empty (c := c) hv hmono hsub hB.le hm
  have hcB : ∀ j ∈ Q, c j ≤ B := fun j hj =>
    (Finset.single_le_sum (fun i _ => hc i) hj).trans hQc
  have key : ∀ j ∈ Q, marg v {j} W * B ≤ c j * (2 * mval v B) := by
    intro j hj
    have hjW : j ∉ W := by
      have := hQ hj; rw [Finset.mem_sdiff] at this; exact this.2
    have hjA : j ∉ (PS v c B 1).A := by
      intro hjA
      rw [← hsF] at hjA
      rcases pool_empty_mem hpool hjA with h | h
      · exact hjW (Finset.mem_union_left _ (by rw [e1]; exact List.mem_toFinset.2 h))
      · exact hjW (Finset.mem_union_right _ (by rw [e2]; exact List.mem_toFinset.2 h))
    obtain ⟨k', hk1, hkK, hkL, hjA1, hjA2⟩ := rej_phase (c := c) hmono hv hB.le (by omega) hjA
    have hk' : k' = 1 := by omega
    subst hk'
    obtain ⟨i, hi, _, hm1⟩ := rej_record (c := c) hmono hv hB hm hk1 hkL hjA1 hjA2 (hcB j hj)
    have hsubW : ((PS v c B 1).cur.take i).toFinset ⊆ W := by
      refine (take_toFinset_sub _ i).trans ?_
      intro x hx; apply Finset.mem_union_right; rw [e2, hsF]; exact hx
    have h2 := marg_anti hmono hsub {j} hsubW
    simp only [pow_one] at hm1
    nlinarith
  have h3 := marg_le_sum hmono hsub W Q
  have h4 : ∑ j ∈ Q, marg v {j} W ≤ (∑ j ∈ Q, c j) * (2 * mval v B) / B := by
    rw [le_div_iff₀ hB, Finset.sum_mul, Finset.sum_mul]
    exact Finset.sum_le_sum key
  have h5 : (∑ j ∈ Q, c j) * (2 * mval v B) / B ≤ 2 * mval v B := by
    rw [div_le_iff₀ hB]
    have : 0 ≤ 2 * mval v B := by positivity
    nlinarith
  linarith

end BCMCore

namespace BCMCore
open BudgetClock.Monotone

variable {n : ℕ}

theorem take_U {α : Type} (S U : List α) (hU : U = S ∨ ∃ j, U = S ++ [j]) (k : ℕ)
    (hk : k ≤ S.length) : U.take k = S.take k := by
  rcases hU with rfl | ⟨j, rfl⟩
  · rfl
  · exact List.take_append_of_le_length hk

theorem prev_dropLast_val {v : Finset (Fin n) → ℝ} {c : Fin n → ℝ} {B : ℝ} (hv : ∀ S, 0 ≤ v S)
    (hmono : IsMonotone v) (hB : 0 ≤ B) {l : ℕ} (hl : lastPhase v c B = l + 3) :
    v (PS v c B (l + 1)).cur.dropLast.toFinset ≤ 2 ^ (l + 1) * mval v B := by
  obtain ⟨hI, _⟩ := phase_facts (c := c) hv hmono hB (k := l) (by omega)
  have htg := (PS_t_tgt (c := c) hv hmono hB (k := l + 1) (by omega)).2
  by_cases hne : (PS v c B (l + 1)).cur = []
  · rw [hne]; simp
    have := v_empty_le_mval hmono (v := v) B
    have h1 : (1:ℝ) ≤ 2 ^ (l + 1) := one_le_pow₀ (by norm_num)
    have := mval_nonneg hv B
    nlinarith
  · have hb : v (PS v c B (l + 1)).cur.dropLast.toFinset < (PS v c B (l + 1)).tgt := by
      rw [List.dropLast_eq_take]
      exact hI.below _ (by have := List.length_pos_iff.2 hne; omega)
    rw [htg] at hb; exact hb.le

/-- Case A of Lemma 10 (`t̂ ≥ 3`, `S_t̂` itself over budget). -/
theorem lemma10_caseA {v : Finset (Fin n) → ℝ} (hv : ∀ S, 0 ≤ v S) (hmono : IsMonotone v)
    (hsub : NonmonotoneSubmod.Shared.Submodular v) (c : Fin n → ℝ)
    (B : ℝ) (hB : 0 < B) {l : ℕ} (hl : lastPhase v c B = l + 3)
    (hU : W2bar v c B = (PS v c B (l + 2)).cur ∨ ∃ j, W2bar v c B = (PS v c B (l + 2)).cur ++ [j])
    (hpS : ∀ i ∈ (PS v c B (l + 2)).cur, finalPrices v c B i = (PS v c B (l + 2)).p i)
    (hinfS : B < listCost (PS v c B (l + 2)).p (PS v c B (l + 2)).cur)
    (O : Finset (Fin n))
    (hOle : v O ≤ 2 ^ (l + 1) * mval v B + mval v B + v (PS v c B (l + 2)).cur.toFinset +
      (3 * 2 ^ (l + 1) * mval v B - 2 * mval v B)) :
    v O ≤ (15 / 4 : ℝ) * v (W3 v c B).toFinset := by
  set S := (PS v c B (l + 2)).cur with hS
  set m := mval v B with hm
  obtain ⟨hI, _⟩ := phase_facts (c := c) hv hmono hB.le (k := l + 1) (by omega)
  have g := GInv.all (c := c) hv hmono hB.le (l + 2)
  have hne : S ≠ [] := by intro h; rw [h] at hinfS; simp [listCost] at hinfS; linarith
  have hK : 0 < S.length := List.length_pos_iff.2 hne
  -- `W2 = S.dropLast`
  have hW2 : W2 v c B = S.dropLast := by
    unfold W2 mvW2
    have hp : ∀ i ∈ W2bar v c B, 0 ≤ finalPrices v c B i :=
      fun i _ => final_p_nonneg (c := c) hv hmono hB.le i
    have hlen : S.length - 1 < (W2bar v c B).length := by
      rcases hU with h | ⟨j, h⟩ <;> rw [h] <;> simp <;> omega
    rw [lfp_eq _ hp (S.length - 1) hlen, take_U S _ hU _ (by omega), ← List.dropLast_eq_take]
    · rw [take_U S _ hU _ (by omega), ← List.dropLast_eq_take,
        listCost_congr (fun i hi => hpS i (List.dropLast_subset _ hi))]
      exact hI.cost_dropLast hv hB.le
    · rw [take_U S _ hU _ (by omega), show S.length - 1 + 1 = S.length by omega, List.take_length,
        listCost_congr hpS]
      exact hinfS
  obtain ⟨K, hKbig, hKD, hτS⟩ := lemma3_aux hv hmono hsub c B hB (l + 1) (by omega) hinfS
  have htg := (PS_t_tgt (c := c) hv hmono hB.le (k := l + 2) (by omega)).2
  rw [htg] at hτS
  have hW3 := W2_le_W3 hmono c B
  rw [hW2] at hW3
  -- `v(S) ≤ v(D) + m`
  have hsplit := val_dropLast (v := v) S hne
  have hδ := marg_single_le hv hsub m (single_le_mval v B) (S[S.length - 1]'(by omega))
    S.dropLast.toFinset
  set D := v S.dropLast.toFinset with hD
  have hm0 := mval_nonneg hv B
  have hD0 : 0 ≤ D := hv _
  -- `τ ≤ (5/4) v(D)`
  have hK5 : (2:ℝ) ^ (l + 2) + 1 ≤ K := by exact_mod_cast hKbig
  have h4 : (4:ℝ) ≤ 2 ^ (l + 2) := by
    have : (4:ℝ) = 2 ^ 2 := by norm_num
    rw [this]; exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hKpos : (5:ℝ) ≤ K := by linarith
  have hτD : 4 * (2 ^ (l + 2) * m) ≤ 5 * D := by
    have h1 : (K - 1) * (2 ^ (l + 2) * m) ≤ K * D := by nlinarith
    nlinarith
  have e : (2:ℝ) ^ (l + 2) = 2 * 2 ^ (l + 1) := by rw [pow_succ]; ring
  rw [e] at hτD
  nlinarith

/-- Case B of Lemma 10 (`t̂ ≥ 3`, `S_t̂` within budget but `S_t̂ + j*` over budget). -/
theorem lemma10_caseB {v : Finset (Fin n) → ℝ} (hv : ∀ S, 0 ≤ v S) (hmono : IsMonotone v)
    (hsub : NonmonotoneSubmod.Shared.Submodular v) (c : Fin n → ℝ)
    (B : ℝ) (hB : 0 < B) {l : ℕ} (hl : lastPhase v c B = l + 3) (hm : 0 < mval v B) (j : Fin n)
    (hU : W2bar v c B = (PS v c B (l + 2)).cur ++ [j])
    (hpS : ∀ i ∈ (PS v c B (l + 2)).cur, finalPrices v c B i = (PS v c B (l + 2)).p i)
    (hpj : finalPrices v c B j * (PS v c B (l + 2)).tgt ≤ B * mval v B)
    (hfeasS : listCost (PS v c B (l + 2)).p (PS v c B (l + 2)).cur ≤ B)
    (hinf : B < listCost (finalPrices v c B) (W2bar v c B))
    (O : Finset (Fin n))
    (hOle : v O ≤ 2 ^ (l + 1) * mval v B + mval v B + v (PS v c B (l + 2)).cur.toFinset +
      (3 * 2 ^ (l + 1) * mval v B - 2 * mval v B)) :
    v O ≤ (15 / 4 : ℝ) * v (W3 v c B).toFinset := by
  set S := (PS v c B (l + 2)).cur with hS
  set m := mval v B with hmd
  obtain ⟨hI, _⟩ := phase_facts (c := c) hv hmono hB.le (k := l + 1) (by omega)
  have htg := (PS_t_tgt (c := c) hv hmono hB.le (k := l + 2) (by omega)).2
  have hτ : 0 < (PS v c B (l + 2)).tgt := by rw [htg]; positivity
  have hW2 : W2 v c B = S := by
    unfold W2 mvW2
    have hp : ∀ i ∈ W2bar v c B, 0 ≤ finalPrices v c B i :=
      fun i _ => final_p_nonneg (c := c) hv hmono hB.le i
    have hlen : S.length < (W2bar v c B).length := by rw [hU]; simp
    rw [lfp_eq _ hp S.length hlen, hU, List.take_append_of_le_length le_rfl, List.take_length]
    · rw [hU, List.take_append_of_le_length le_rfl, List.take_length, listCost_congr hpS]
      exact hfeasS
    · rw [hU, show S.length + 1 = (S ++ [j]).length by simp, List.take_length]
      rw [hU] at hinf; exact hinf
  have hW3 := W2_le_W3 hmono c B
  rw [hW2] at hW3
  -- `τ < v(S) + m`
  have hcost := cost_le_of_marg (v := v) (p := (PS v c B (l + 2)).p)
    (τ := (PS v c B (l + 2)).tgt) (B := B) S (fun k hk => hI.price_le hτ k hk)
  rw [hU, listCost_append_single, listCost_congr hpS] at hinf
  have hv0 := hv ∅
  have hτS : (PS v c B (l + 2)).tgt < v S.toFinset + m := by
    have h1 : B * (PS v c B (l + 2)).tgt < (listCost (PS v c B (l + 2)).p S +
        finalPrices v c B j) * (PS v c B (l + 2)).tgt := mul_lt_mul_of_pos_right hinf hτ
    have h2 : B * (PS v c B (l + 2)).tgt < B * (v S.toFinset - v ∅) + B * m := by nlinarith
    have h3 : B * (PS v c B (l + 2)).tgt < B * (v S.toFinset + m) := by nlinarith
    exact lt_of_mul_lt_mul_left h3 hB.le
  rw [htg] at hτS
  have e : (2:ℝ) ^ (l + 2) = 2 * 2 ^ (l + 1) := by rw [pow_succ]; ring
  rw [e] at hτS
  have h2 : (2:ℝ) ≤ 2 ^ (l + 1) := by
    calc (2:ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (l + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hS0 : 0 ≤ v S.toFinset := hv _
  nlinarith

end BCMCore

namespace BCMCore
open BudgetClock.Monotone

variable {n : ℕ}

theorem PS0_cur_val (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (B : ℝ) :
    v (PS v c B 0).cur.toFinset = mval v B := rfl

theorem init_cost_le (v : Finset (Fin n) → ℝ) {B : ℝ} (hB : 0 ≤ B) :
    listCost (initState v B).p (initState v B).cur ≤ B := by
  unfold initState; simp only
  split_ifs <;> simp [listCost] <;> exact hB

/-- **Lemma 10**. -/
theorem lemma10_core {v : Finset (Fin n) → ℝ} (hv : ∀ S, 0 ≤ v S) (hmono : IsMonotone v)
    (hsub : NonmonotoneSubmod.Shared.Submodular v) (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i)
    (B : ℝ) (hB : 0 < B) (hinf : B < listCost (finalPrices v c B) (W2bar v c B)) :
    ∀ O : Finset (Fin n), ∑ i ∈ O, c i ≤ B → v O ≤ (15 / 4 : ℝ) * v (W3 v c B).toFinset := by
  intro O hO
  rcases (mval_nonneg hv B).lt_or_eq with hm | hm
  swap
  · have h0 := v_zero_of_mval_zero hv hmono hsub hm.symm
    rw [h0, h0]; norm_num
  set W := (W1 v c B).toFinset ∪ (W2bar v c B).toFinset with hW
  obtain ⟨Q, hQ, hQc, hOQ⟩ := benchmark_core hmono c hc B W O hO
  have hsa := subadd hv hsub (W1 v c B).toFinset (W2bar v c B).toFinset
  have hL := lastPhase_ge v c B
  have hpr : pruned v c B = prune v c B (finalState v c B) := rfl
  set m := mval v B with hmd
  rcases Nat.lt_or_ge (lastPhase v c B) 2 with h1 | h2
  · exfalso
    have e : finalState v c B = PS v c B 0 := by rw [final_eq, show lastPhase v c B - 1 = 0 by omega]
    unfold W2bar finalPrices at hinf
    rw [hpr] at hinf
    rcases prune_cases v c hB.le (finalState v c B) with ⟨_, he⟩ | ⟨hb, _, _, _⟩
    · rw [he, e, PS_zero] at hinf
      have := init_cost_le v hB.le (B := B)
      simp only at hinf
      linarith
    · rw [e, PS_zero] at hb; simp [initState, listCost] at hb; linarith
  rcases Nat.lt_or_ge (lastPhase v c B) 3 with h2' | h3
  · -- `t̂ = 2`
    have hL2 : lastPhase v c B = 2 := by omega
    have hnp := no_prune_L2 (c := c) hv hmono hB.le hL2
    have hsF : finalState v c B = PS v c B 1 := by rw [final_eq, hL2]
    have e1 : W1 v c B = (PS v c B 0).cur := by
      unfold W1; rw [hnp]; simp only
      rw [(final_prev (c := c) hv hmono hB.le (by omega)).1, hL2]
    have e2 : W2bar v c B = (PS v c B 1).cur := by unfold W2bar; rw [hnp, hsF]
    have e3 : finalPrices v c B = (PS v c B 1).p := by unfold finalPrices; rw [hnp, hsF]
    have hβ := beta_L2 hv hmono hsub c hc B hB hL2 hm Q hQ hQc
    rw [e2, e3] at hinf
    obtain ⟨K, hKbig, hKD, hτS⟩ := lemma3_aux hv hmono hsub c B hB 0 (by omega) hinf
    have htg := (PS_t_tgt (c := c) hv hmono hB.le (k := 1) (by omega)).2
    rw [htg] at hτS
    obtain ⟨hI, _⟩ := phase_facts (c := c) hv hmono hB.le (k := 0) (by omega)
    set S := (PS v c B 1).cur with hS
    have hne : S ≠ [] := by intro h; rw [h] at hinf; simp [listCost] at hinf; linarith
    have hK : 0 < S.length := List.length_pos_iff.2 hne
    have hW2 : W2 v c B = S.dropLast := by
      unfold W2 mvW2
      rw [e2, e3]
      have g := GInv.all (c := c) hv hmono hB.le 1
      rw [lfp_eq _ (fun i _ => g.p_nn i) (S.length - 1) (by omega), ← List.dropLast_eq_take]
      · rw [← List.dropLast_eq_take]; exact hI.cost_dropLast hv hB.le
      · rw [show S.length - 1 + 1 = S.length by omega, List.take_length]; exact hinf
    have hW3 := W2_le_W3 hmono c B
    rw [hW2] at hW3
    have hsa' : v W ≤ m + v S.toFinset := by
      rw [hW]; rw [e1, PS0_cur_val v c B, e2] at hsa; rw [e1, e2]; exact hsa
    rw [← hW] at hβ
    have hK3 : (3:ℝ) ≤ K := by exact_mod_cast hKbig
    have hD0 : 0 ≤ v S.dropLast.toFinset := hv _
    have hS0 : 0 ≤ v S.toFinset := hv _
    simp only [pow_one] at hτS
    have hKpos : (0:ℝ) < K := by linarith
    have h1 : 2 * (K : ℝ) * v S.toFinset ≤ 3 * ((K : ℝ) - 1) * v S.toFinset := by
      have : 0 ≤ ((K : ℝ) - 3) * v S.toFinset := mul_nonneg (by linarith) hS0
      linarith
    have h2 : 3 * ((K : ℝ) - 1) * v S.toFinset ≤ 3 * (K : ℝ) * v S.dropLast.toFinset := by
      linarith
    have h3 : (K : ℝ) * (2 * v S.toFinset) ≤ (K : ℝ) * (3 * v S.dropLast.toFinset) := by
      linarith
    have hDS : 2 * v S.toFinset ≤ 3 * v S.dropLast.toFinset := le_of_mul_le_mul_left h3 hKpos
    linarith
  · -- `t̂ ≥ 3`
    obtain ⟨l, hl⟩ : ∃ l, lastPhase v c B = l + 3 := ⟨lastPhase v c B - 3, by omega⟩
    have hβ := lemma2_core hv hmono hsub c hc B hB h3 Q hQ hQc
    have htarget : target v c B (lastPhase v c B) = 2 ^ (l + 2) * m := by
      unfold target; rw [phaseState_eq, hl]
      exact (PS_t_tgt (c := c) hv hmono hB.le (k := l + 2) (by omega)).2
    rw [htarget, hl, show l + 3 - 2 = l + 1 by omega] at hβ
    have hβ' : marg v Q W ≤ 3 * 2 ^ (l + 1) * m - 2 * m := by
      have e : (3 / 2 - 1 / (2:ℝ) ^ (l + 1)) * (2 ^ (l + 2) * m) = 3 * 2 ^ (l + 1) * m - 2 * m := by
        rw [pow_succ]; field_simp; ring
      rw [← e]; exact hβ
    have hsF : finalState v c B = PS v c B (l + 2) := by
      rw [final_eq, hl, show l + 3 - 1 = l + 2 by omega]
    obtain ⟨hprev, hprevp⟩ := final_prev (c := c) hv hmono hB.le (by omega)
    rw [hl, show l + 3 - 2 = l + 1 by omega] at hprev hprevp
    have hpd := prev_dropLast_val (c := c) hv hmono hB.le hl
    have g := GInv.all (c := c) hv hmono hB.le (l + 2)
    rw [← hsF] at g
    have hm1 := single_le_mval v B
    -- `v(S_{t̂-1}) ≤ v(S_{t̂-1}.dropLast) + m`
    have hpv : v (PS v c B (l + 1)).cur.toFinset ≤ 2 ^ (l + 1) * m + m := by
      by_cases hne : (PS v c B (l + 1)).cur = []
      · rw [hne] at hpd ⊢; simp at hpd ⊢; linarith
      · have hs := val_dropLast (v := v) _ hne
        have := marg_single_le hv hsub m hm1 ((PS v c B (l + 1)).cur[(PS v c B (l + 1)).cur.length - 1]'(by
          have := List.length_pos_iff.2 hne; omega)) (PS v c B (l + 1)).cur.dropLast.toFinset
        linarith
    have hOle0 : v O ≤ v (W1 v c B).toFinset + v (W2bar v c B).toFinset +
        (3 * 2 ^ (l + 1) * m - 2 * m) := by linarith
    unfold W1 W2bar at hOle0
    rw [hpr] at hOle0
    rcases prune_cases v c hB.le (finalState v c B) with ⟨hb, he⟩ | ⟨hb, j0, hj0, hcase⟩
    · -- no pruning
      rw [he] at hOle0
      simp only at hOle0
      have hU : W2bar v c B = (PS v c B (l + 2)).cur := by unfold W2bar; rw [hpr, he, hsF]
      have hpS : ∀ i ∈ (PS v c B (l + 2)).cur, finalPrices v c B i = (PS v c B (l + 2)).p i := by
        intro i _; unfold finalPrices; rw [hpr, he, hsF]
      have hinfS : B < listCost (PS v c B (l + 2)).p (PS v c B (l + 2)).cur := by
        rw [hU, listCost_congr hpS] at hinf; exact hinf
      apply lemma10_caseA hv hmono hsub c B hB hl (Or.inl hU) hpS hinfS O
      rw [hprev, hsF] at hOle0
      linarith
    · simp only at hcase
      have hj0p : j0 ∈ (finalState v c B).prev := by
        have hne : (finalState v c B).prev ≠ [] := by intro h; rw [h] at hj0; simp at hj0
        rw [List.getLast?_eq_some_getLast hne, Option.some.injEq] at hj0
        rw [← hj0]; exact List.getLast_mem hne
      have hj0S : j0 ∉ (PS v c B (l + 2)).cur := by
        intro h; rw [← hsF] at h; exact g.disj j0 h hj0p
      have hW1v : v (finalState v c B).prev.dropLast.toFinset ≤ 2 ^ (l + 1) * m := by
        rw [hprev]; exact hpd
      rcases hcase with ⟨hacc, he⟩ | ⟨_, he⟩
      · -- pruned bidder accepted
        rw [he] at hOle0
        simp only at hOle0
        have hU : W2bar v c B = (PS v c B (l + 2)).cur ++ [j0] := by
          unfold W2bar; rw [hpr, he, hsF]
        have hpS : ∀ i ∈ (PS v c B (l + 2)).cur, finalPrices v c B i =
            (PS v c B (l + 2)).p i := by
          intro i hi; unfold finalPrices; rw [hpr, he]; simp only
          rw [Function.update_of_ne (fun (h : i = j0) => hj0S (by rw [← h]; exact hi)), hsF]
        have hUv : v ((finalState v c B).cur ++ [j0]).toFinset ≤
            v (PS v c B (l + 2)).cur.toFinset + m := by
          have e : ((finalState v c B).cur ++ [j0]).toFinset =
              (PS v c B (l + 2)).cur.toFinset ∪ {j0} := by
            rw [hsF]; simp only [List.toFinset_append, List.toFinset_cons, List.toFinset_nil,
              insert_empty_eq]
          rw [e]
          have := subadd hv hsub (PS v c B (l + 2)).cur.toFinset {j0}
          linarith [hm1 j0]
        have hOle : v O ≤ 2 ^ (l + 1) * m + m + v (PS v c B (l + 2)).cur.toFinset +
            (3 * 2 ^ (l + 1) * m - 2 * m) := by linarith
        by_cases hS : B < listCost (PS v c B (l + 2)).p (PS v c B (l + 2)).cur
        · exact lemma10_caseA hv hmono hsub c B hB hl (Or.inr ⟨j0, hU⟩) hpS hS O hOle
        · apply lemma10_caseB hv hmono hsub c B hB hl hm j0 hU hpS _ (le_of_not_gt hS) hinf O hOle
          have htg := (PS_t_tgt (c := c) hv hmono hB.le (k := l + 2) (by omega)).2
          have hτ : 0 < (PS v c B (l + 2)).tgt := by rw [htg]; positivity
          unfold finalPrices; rw [hpr, he]; simp only [Function.update_self]
          have h1 : min ((finalState v c B).p j0)
              (marg v {j0} (finalState v c B).cur.toFinset * B / (finalState v c B).tgt) ≤
              marg v {j0} (finalState v c B).cur.toFinset * B / (finalState v c B).tgt :=
            min_le_right _ _
          rw [hsF] at h1 ⊢
          rw [le_div_iff₀ hτ] at h1
          have h2 := marg_single_le hv hsub m hm1 j0 (PS v c B (l + 2)).cur.toFinset
          nlinarith
      · -- pruned bidder rejected
        rw [he] at hOle0
        simp only at hOle0
        have hU : W2bar v c B = (PS v c B (l + 2)).cur := by unfold W2bar; rw [hpr, he, hsF]
        have hpS : ∀ i ∈ (PS v c B (l + 2)).cur, finalPrices v c B i =
            (PS v c B (l + 2)).p i := by
          intro i hi; unfold finalPrices; rw [hpr, he]; simp only
          rw [Function.update_of_ne (fun (h : i = j0) => hj0S (by rw [← h]; exact hi)), hsF]
        have hinfS : B < listCost (PS v c B (l + 2)).p (PS v c B (l + 2)).cur := by
          rw [hU, listCost_congr hpS] at hinf; exact hinf
        apply lemma10_caseA hv hmono hsub c B hB hl (Or.inl hU) hpS hinfS O
        have hcur : (finalState v c B).cur = (PS v c B (l + 2)).cur := by rw [hsF]
        rw [hcur] at hOle0
        linarith

end BCMCore

namespace BCMCore
open BudgetClock.Monotone

variable {n : ℕ}

theorem lfp_full {p : Fin n → ℝ} {B : ℝ} (U : List (Fin n)) (h : listCost p U ≤ B) :
    longestFeasiblePrefix p B U = U := by
  unfold longestFeasiblePrefix
  rw [Nat.findGreatest_eq (by rw [List.take_length]; exact h), List.take_length]

/-- **Lemma 9**. -/
theorem lemma9_core {v : Finset (Fin n) → ℝ} (hv : ∀ S, 0 ≤ v S) (hmono : IsMonotone v)
    (hsub : NonmonotoneSubmod.Shared.Submodular v) (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i)
    (B : ℝ) (hB : 0 < B) (h2 : lastPhase v c B ≤ 2) :
    ∀ O : Finset (Fin n), ∑ i ∈ O, c i ≤ B → v O ≤ 4 * v (iterativePruning v c B).1 := by
  intro O hO
  rcases (mval_nonneg hv B).lt_or_eq with hm | hm
  swap
  · have h0 := v_zero_of_mval_zero hv hmono hsub hm.symm
    rw [h0, h0]; norm_num
  obtain ⟨hWW1, hWW3⟩ := W_ge v c B
  have hW0 := hv (iterativePruning v c B).1
  have hL := lastPhase_ge v c B
  have hpr : pruned v c B = prune v c B (finalState v c B) := rfl
  rcases Nat.lt_or_ge (lastPhase v c B) 2 with h1 | h2'
  · -- `t̂ = 1`: every bidder is in `S_1`
    have e : finalState v c B = PS v c B 0 := by rw [final_eq, show lastPhase v c B - 1 = 0 by omega]
    have hpool := final_pool_empty (c := c) hv hmono hsub hB.le hm
    rw [e] at hpool
    have hnp : pruned v c B = ((PS v c B 0).prev, (PS v c B 0).cur, (PS v c B 0).p) := by
      rw [hpr, e]
      rcases prune_cases v c hB.le (PS v c B 0) with ⟨_, he⟩ | ⟨hb, _, _, _⟩
      · exact he
      · exfalso; simp [PS_zero, initState, listCost] at hb; linarith
    have hW2 : W2 v c B = (PS v c B 0).cur := by
      unfold W2 mvW2
      have e2 : W2bar v c B = (PS v c B 0).cur := by unfold W2bar; rw [hnp]
      have e3 : finalPrices v c B = (PS v c B 0).p := by unfold finalPrices; rw [hnp]
      rw [e2, e3]
      exact lfp_full _ (init_cost_le v hB.le)
    have hOsub : O ⊆ (W3 v c B).toFinset := by
      intro x _
      have hxA : x ∈ (PS v c B 0).A := by simp [PS_zero, initState]
      rcases pool_empty_mem hpool hxA with h | h
      · simp [PS_zero, initState] at h
      · unfold W3; rw [hW2]; simp only [List.mem_toFinset, List.mem_append]; exact Or.inl h
    have := hmono _ _ hOsub
    linarith
  · have hL2 : lastPhase v c B = 2 := by omega
    by_cases hinf : B < listCost (finalPrices v c B) (W2bar v c B)
    · have := lemma10_core hv hmono hsub c hc B hB hinf O hO
      have h3 := hv (W3 v c B).toFinset
      linarith
    · -- `W̄_2` is affordable, so `W_2 = W̄_2`
      have hnp := no_prune_L2 (c := c) hv hmono hB.le hL2
      have hsF : finalState v c B = PS v c B 1 := by rw [final_eq, hL2]
      have e1 : W1 v c B = (PS v c B 0).cur := by
        unfold W1; rw [hnp]; simp only
        rw [(final_prev (c := c) hv hmono hB.le (by omega)).1, hL2]
      have hW2 : W2 v c B = W2bar v c B := by
        unfold W2 mvW2; exact lfp_full _ (le_of_not_gt hinf)
      set W := (W1 v c B).toFinset ∪ (W2bar v c B).toFinset with hW
      obtain ⟨Q, hQ, hQc, hOQ⟩ := benchmark_core hmono c hc B W O hO
      have hβ := beta_L2 hv hmono hsub c hc B hB hL2 hm Q hQ hQc
      rw [← hW] at hβ
      have hsa := subadd hv hsub (W1 v c B).toFinset (W2bar v c B).toFinset
      rw [← hW] at hsa
      have hW1v : v (W1 v c B).toFinset = mval v B := by rw [e1]; rfl
      have hW23 := W2_le_W3 hmono c B
      rw [hW2] at hW23
      linarith

end BCMCore

open BudgetClock.Monotone in
theorem solution {n : ℕ} (v : Finset (Fin n) → ℝ) (hv : ∀ S, 0 ≤ v S) (hmono : IsMonotone v)
    (hsub : NonmonotoneSubmod.Shared.Submodular v) (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i)
    (B : ℝ) (hB : 0 < B) (h2 : lastPhase v c B ≤ 2) :
    ∀ O : Finset (Fin n), ∑ i ∈ O, c i ≤ B → v O ≤ 4 * v (iterativePruning v c B).1 :=
  BCMCore.lemma9_core hv hmono hsub c hc B hB h2
