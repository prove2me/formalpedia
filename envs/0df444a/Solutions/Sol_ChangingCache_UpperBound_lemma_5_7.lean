-- Prove2me | solution 1 for ChangingCache.UpperBound.lemma_5_7
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T18:53:31.104621+00:00
-- url     : https://prove2.me/submissions/d5f77cf1-161f-4c64-bfef-8be558b21070

import Mathlib
import Definitions.Def_ChangingCache_UpperBound_Bank
import Theorems.Thm_ChangingCache_UpperBound_observation_3_1

open ChangingCache.UpperBound

namespace Keep57Aux

variable {α : Type*} [DecidableEq α]

theorem lruRun_succ (C : ℕ → ℕ) (σ : List α) (k : ℕ) (hk : k < σ.length) :
    lruRun C (σ.take (k + 1)) = lruStep C (lruRun C (σ.take k)) σ[k] := by
  unfold lruRun
  rw [List.take_add_one, List.getElem?_eq_getElem hk, List.foldl_append]
  rfl

theorem lru_misses (C : ℕ → ℕ) (σ : List α) (h1 : LRUAlwaysMisses C σ) :
    ∀ k ≤ σ.length, (lruRun C (σ.take k)).misses = k := by
  intro k
  induction k with
  | zero =>
    intro _
    simp [lruRun]
  | succ k ih =>
    intro hk
    have hk' : k < σ.length := by omega
    have hm := ih (by omega)
    rw [lruRun_succ C σ k hk']
    unfold lruStep
    rw [if_neg (h1 k hk')]
    simp [hm]

/-- Two capacity laws that agree on `1, …, r` give the same LRU run on the first `r` requests
of a sequence that always misses. -/
theorem lru_agree (C C' : ℕ → ℕ) (σ : List α) (h1 : LRUAlwaysMisses C σ) (r : ℕ)
    (hr : r ≤ σ.length) (hC : ∀ k, 1 ≤ k → k ≤ r → C' k = C k) :
    ∀ u ≤ r, lruRun C' (σ.take u) = lruRun C (σ.take u) := by
  intro u
  induction u with
  | zero => intro _; rfl
  | succ u ih =>
    intro hu
    have hu' : u < σ.length := by omega
    rw [lruRun_succ C' σ u hu', lruRun_succ C σ u hu', ih (by omega)]
    have hmis := lru_misses C σ h1 u (by omega)
    unfold lruStep
    rw [hmis, hC (u + 1) (by omega) hu]

theorem policyMisses_succ (σ : List α) (S : ℕ → Finset α) (k : ℕ) :
    policyMisses σ S (k + 1) = policyMisses σ S k + if missB σ S k then 1 else 0 := by
  cases h : missB σ S k <;> simp [policyMisses, List.range_succ, List.filter_append, h]

theorem policyMisses_mono (σ : List α) (S : ℕ → Finset α) {a b : ℕ} (hab : a ≤ b) :
    policyMisses σ S a ≤ policyMisses σ S b := by
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ b _ ih =>
    rw [policyMisses_succ]
    omega

theorem missB_take (σ : List α) (T : ℕ → Finset α) {r i : ℕ} (hi : i < r) :
    missB (σ.take r) T i = missB σ T i := by
  unfold missB
  rw [List.getElem?_take, if_pos hi]

theorem missB_iff (σ : List α) (T : ℕ → Finset α) {i : ℕ} (hi : i < σ.length) :
    missB σ T i = true ↔ σ[i] ∉ T i := by
  unfold missB
  rw [List.getElem?_eq_getElem hi]
  simp

theorem getElem_mem_take (σ : List α) {i' i : ℕ} (h : i' < i) (hi : i ≤ σ.length) :
    σ[i'] ∈ σ.take i := by
  have hlt : i' < (σ.take i).length := by rw [List.length_take]; omega
  have : (σ.take i)[i'] = σ[i'] := List.getElem_take
  rw [← this]
  exact List.getElem_mem _

theorem mem_take_mono (σ : List α) {x : α} {a b : ℕ} (hx : x ∈ σ.take a) (hab : a ≤ b) :
    x ∈ σ.take b := by
  have : σ.take a = (σ.take b).take a := by
    rw [List.take_take, Nat.min_eq_left hab]
  rw [this] at hx
  exact List.mem_of_mem_take hx

theorem seen (m : ℕ → ℕ) (σ : List α) (T : ℕ → Finset α) (hT : IsLegal m σ T) :
    ∀ i ≤ σ.length, ∀ x ∈ T i, x ∈ σ.take i := by
  intro i
  induction i with
  | zero =>
    intro _ x hx
    rw [hT.1] at hx
    simp at hx
  | succ i ih =>
    intro hi x hx
    have hi' : i < σ.length := by omega
    have h1 := (hT.2 i hi').1 hx
    rw [Finset.mem_insert] at h1
    rw [List.take_add_one, List.getElem?_eq_getElem hi']
    simp only [List.mem_append, Option.toList_some, List.mem_singleton]
    rcases h1 with h | h
    · exact Or.inr h
    · exact Or.inl (ih (by omega) x h)

theorem mem_loadedIn (σ : List α) (S : ℕ → Finset α) (r' u : ℕ) (x : α) :
    x ∈ loadedIn σ S r' u ↔
      ∃ i, r' ≤ i ∧ i < u ∧ missB σ S i = true ∧ σ[i]? = some x := by
  unfold loadedIn
  rw [List.mem_toFinset, List.mem_filterMap]
  constructor
  · rintro ⟨i, hi, h⟩
    rw [List.mem_range] at hi
    split_ifs at h with hc
    exact ⟨i, hc.1, hi, hc.2, h⟩
  · rintro ⟨i, h1, h2, h3, h4⟩
    exact ⟨i, List.mem_range.2 h2, by rw [if_pos ⟨h1, h3⟩]; exact h4⟩

/-- Pages loaded at cold misses in `[r', u)` are new and distinct: there are exactly as many as
misses. -/
theorem loadedIn_card (σ : List α) (S : ℕ → Finset α) (hcold : AllMissesCold σ S) (r' : ℕ) :
    ∀ u, r' ≤ u → u ≤ σ.length →
      (loadedIn σ S r' u).card + policyMisses σ S r' = policyMisses σ S u := by
  intro u hu
  induction u, hu using Nat.le_induction with
  | base =>
    intro _
    have : loadedIn σ S r' r' = ∅ := by
      ext x
      rw [mem_loadedIn]
      simp only [Finset.notMem_empty, iff_false]
      rintro ⟨i, h1, h2, _⟩
      omega
    rw [this]
    simp
  | succ u hu ih =>
    intro hlen
    have hu' : u < σ.length := by omega
    have ih := ih (by omega)
    rw [policyMisses_succ]
    by_cases hmiss : missB σ S u = true
    · have heq : loadedIn σ S r' (u + 1) = insert σ[u] (loadedIn σ S r' u) := by
        ext x
        rw [Finset.mem_insert, mem_loadedIn, mem_loadedIn]
        constructor
        · rintro ⟨i, h1, h2, h3, h4⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 h2 with h | h
          · exact Or.inr ⟨i, h1, h, h3, h4⟩
          · subst h
            rw [List.getElem?_eq_getElem hu', Option.some.injEq] at h4
            exact Or.inl h4.symm
        · rintro (h | ⟨i, h1, h2, h3, h4⟩)
          · exact ⟨u, hu, by omega, hmiss, by rw [h, List.getElem?_eq_getElem hu']⟩
          · exact ⟨i, h1, by omega, h3, h4⟩
      have hnot : σ[u] ∉ loadedIn σ S r' u := by
        rw [mem_loadedIn]
        rintro ⟨i, _, h2, _, h4⟩
        obtain ⟨_, hc⟩ := hcold u hu' hmiss
        have hi : i < σ.length := by omega
        rw [List.getElem?_eq_getElem hi, Option.some.injEq] at h4
        apply hc
        rw [← h4]
        exact getElem_mem_take σ h2 (le_of_lt hu')
      rw [heq, Finset.card_insert_of_notMem hnot, if_pos hmiss]
      omega
    · have heq : loadedIn σ S r' (u + 1) = loadedIn σ S r' u := by
        ext x
        rw [mem_loadedIn, mem_loadedIn]
        constructor
        · rintro ⟨i, h1, h2, h3, h4⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 h2 with h | h
          · exact ⟨i, h1, h, h3, h4⟩
          · subst h; exact absurd h3 hmiss
        · rintro ⟨i, h1, h2, h3, h4⟩
          exact ⟨i, h1, by omega, h3, h4⟩
      rw [heq, if_neg hmiss]
      omega

theorem held (m : ℕ → ℕ) (σ : List α) (S : ℕ → Finset α) (hS : IsLegal m σ S) (r' : ℕ) :
    ∀ t, r' ≤ t → t ≤ σ.length → S t ⊆ S r' ∪ loadedIn σ S r' t := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base =>
    intro _ x hx
    exact Finset.mem_union_left _ hx
  | succ t ht ih =>
    intro hlen x hx
    have ht' : t < σ.length := by omega
    have h1 := (hS.2 t ht').1 hx
    rw [Finset.mem_insert] at h1
    have mono : ∀ y, y ∈ S r' ∪ loadedIn σ S r' t → y ∈ S r' ∪ loadedIn σ S r' (t + 1) := by
      intro y hy
      rw [Finset.mem_union] at hy ⊢
      rcases hy with hy | hy
      · exact Or.inl hy
      · right
        rw [mem_loadedIn] at hy ⊢
        obtain ⟨i, a, b, c, d⟩ := hy
        exact ⟨i, a, by omega, c, d⟩
    rcases h1 with h | h
    · by_cases hm : σ[t] ∈ S t
      · exact mono x (ih (by omega) (h ▸ hm))
      · apply Finset.mem_union_right
        rw [mem_loadedIn]
        exact ⟨t, ht, by omega, (missB_iff σ S ht').2 hm,
          by rw [List.getElem?_eq_getElem ht', h]⟩
    · exact mono x (ih (by omega) h)

/-- A legal policy holds at most `m (F u)` pages after its `F u`-th miss, and nothing before
its first miss. -/
theorem card_cap (m : ℕ → ℕ) (σ : List α) (S : ℕ → Finset α) (hS : IsLegal m σ S) :
    ∀ u ≤ σ.length, (S u).card ≤
      if policyMisses σ S u = 0 then 0 else m (policyMisses σ S u) := by
  intro u
  induction u with
  | zero =>
    intro _
    rw [hS.1]; simp
  | succ u ih =>
    intro hu
    have hu' : u < σ.length := by omega
    have ih := ih (by omega)
    have hstep := hS.2 u hu'
    rw [policyMisses_succ]
    by_cases hm : σ[u] ∈ S u
    · have hmB : missB σ S u = false := by
        cases h : missB σ S u
        · rfl
        · exact absurd hm ((missB_iff σ S hu').1 h)
      rw [hmB]
      simp only [Bool.false_eq_true, if_false, add_zero]
      have hsub : S (u + 1) ⊆ S u := by
        have := hstep.1
        rwa [Finset.insert_eq_of_mem hm] at this
      exact le_trans (Finset.card_le_card hsub) ih
    · have hmB : missB σ S u = true := (missB_iff σ S hu').2 hm
      rw [hmB]
      simp only [if_true, Nat.add_one_ne_zero, if_false]
      have h2 := hstep.2 hm
      exact le_trans (Finset.card_le_card hstep.1)
        (le_trans (Finset.card_insert_le _ _) h2)

theorem augCap_23 (m : ℕ → ℕ) (k : ℕ) : augCap 2 3 m k = 2 * m (k / 3) := by
  unfold augCap
  rw [Nat.floor_div_ofNat, Nat.floor_natCast]

end Keep57Aux

open Keep57Aux in
theorem solution {α : Type*} [DecidableEq α] (m : ℕ → ℕ) (σ : List α) (S : ℕ → Finset α)
    (hred : IsReduced 2 3 m σ S) (r' r : ℕ) (hrr : r' < r) (hr : r ≤ σ.length)
    (hcond : r ≤ 3 * policyMisses σ S (r' + 1) + 2) :
    ∃ (m' : ℕ → ℕ) (S' : ℕ → Finset α),
      IsReduced 2 3 m' (σ.take r) S' ∧
      (∀ j ≤ policyMisses σ S (r' + 1), m' j = m j) ∧
      (∀ u ≤ r, (lruRun (augCap 2 3 m') (σ.take u)).cache =
        (lruRun (augCap 2 3 m) (σ.take u)).cache) ∧
      (∀ i < r, missB (σ.take r) S' i = missB σ S i) ∧
      (∀ u, r' ≤ u → u ≤ r → S' u = S r' ∪ loadedIn σ S r' u) ∧
      (∀ u, r' ≤ u → u ≤ r →
        bank3 m' (σ.take r) S' u = bank3 m σ S u ∧
        S u ⊆ S' u ∧
        (S' u).card + policyMisses σ S r' = (S r').card + policyMisses σ S u) := by
  obtain ⟨hm, hopt, hR1, hR2, hR3⟩ := hred
  have hS := hopt.1
  have hr'len : r' < σ.length := by omega
  set j0 := policyMisses σ S r' with hj0
  let m' : ℕ → ℕ := fun j => if j ≤ j0 then m j else (S r').card + (j - j0)
  let S' : ℕ → Finset α := fun u => if u < r' then S u else S r' ∪ loadedIn σ S r' u
  have hS'lt : ∀ u, u < r' → S' u = S u := fun u hu => if_pos hu
  have hS'ge : ∀ u, r' ≤ u → S' u = S r' ∪ loadedIn σ S r' u :=
    fun u hu => if_neg (by omega)
  -- the policy `S'` holds a page exactly when `S` does, at the requested page
  have hmemEq : ∀ i (hi : i < σ.length), (σ[i]'hi ∈ S' i ↔ σ[i]'hi ∈ S i) := by
    intro i hi
    by_cases hir : i < r'
    · rw [hS'lt i hir]
    · rw [hS'ge i (by omega)]
      constructor
      · intro hmem
        by_contra hnot
        have hmB : missB σ S i = true := (missB_iff σ S hi).2 hnot
        obtain ⟨_, hc⟩ := hR2 i hi hmB
        apply hc
        rw [Finset.mem_union] at hmem
        rcases hmem with h | h
        · exact mem_take_mono σ (seen m σ S hS r' (by omega) _ h) (by omega)
        · rw [mem_loadedIn] at h
          obtain ⟨t, _, h2, _, h4⟩ := h
          have ht : t < σ.length := by omega
          rw [List.getElem?_eq_getElem ht, Option.some.injEq] at h4
          rw [← h4]
          exact getElem_mem_take σ h2 (le_of_lt hi)
      · intro hmem
        exact held m σ S hS r' i (by omega) (le_of_lt hi) hmem
  have hmissEq : ∀ i < r, missB (σ.take r) S' i = missB σ S i := by
    intro i hi
    rw [missB_take σ S' hi]
    have hi' : i < σ.length := by omega
    have := hmemEq i hi'
    unfold missB
    rw [List.getElem?_eq_getElem hi']
    simp only [this]
  have hPM : ∀ i ≤ r, policyMisses (σ.take r) S' i = policyMisses σ S i := by
    intro i hi
    unfold policyMisses
    congr 1
    apply List.filter_congr
    intro x hx
    rw [List.mem_range] at hx
    exact hmissEq x (by omega)
  have hj0le : ∀ i, r' ≤ i → j0 ≤ policyMisses σ S i := fun i hi => policyMisses_mono σ S hi
  -- card of the kept cache
  have hdisj : ∀ u, Disjoint (S r') (loadedIn σ S r' u) := by
    intro u
    rw [Finset.disjoint_left]
    intro x hx hl
    rw [mem_loadedIn] at hl
    obtain ⟨t, h1, h2, h3, h4⟩ := hl
    have ht : t < σ.length := by
      by_contra hcon
      rw [List.getElem?_eq_none (by omega)] at h4
      simp at h4
    rw [List.getElem?_eq_getElem ht, Option.some.injEq] at h4
    obtain ⟨_, hc⟩ := hR2 t ht h3
    apply hc
    rw [h4]
    exact mem_take_mono σ (seen m σ S hS r' (by omega) x hx) h1
  have hcardS' : ∀ u, r' ≤ u → u ≤ σ.length →
      (S' u).card + j0 = (S r').card + policyMisses σ S u := by
    intro u h1 h2
    rw [hS'ge u h1, Finset.card_union_of_disjoint (hdisj u)]
    have := loadedIn_card σ S hR2 r' u h1 h2
    omega
  -- the new profile agrees with `m` up to `F(r' + 1)`
  have hm'eq : ∀ j ≤ policyMisses σ S (r' + 1), m' j = m j := by
    intro j hj
    by_cases hjj : j ≤ j0
    · exact if_pos hjj
    · have hsucc := policyMisses_succ σ S r'
      have hmB : missB σ S r' = true := by
        by_contra hcon
        rw [if_neg hcon] at hsucc
        omega
      rw [if_pos hmB] at hsucc
      have hj' : j = j0 + 1 := by omega
      have h3 := hR3 r' hr'len hmB
      show (if j ≤ j0 then m j else (S r').card + (j - j0)) = m j
      have h3' : (S r').card + 1 = m (j0 + 1) := h3
      rw [if_neg hjj, hj', ← h3']
      omega
  have hCeq : ∀ k, 1 ≤ k → k ≤ r → augCap 2 3 m' k = augCap 2 3 m k := by
    intro k _ hk
    rw [augCap_23, augCap_23, hm'eq (k / 3) (by omega)]
  have hlru := lru_agree (augCap 2 3 m) (augCap 2 3 m') σ hR1 r hr hCeq
  have hlen : (σ.take r).length = r := by rw [List.length_take]; omega
  -- (R3) for the new run
  have hR3' : ∀ i < (σ.take r).length, missB (σ.take r) S' i = true →
      (S' i).card + 1 = m' (policyMisses (σ.take r) S' i + 1) := by
    intro i hi hmB
    rw [hlen] at hi
    rw [hmissEq i hi] at hmB
    rw [hPM i (le_of_lt hi)]
    have hi' : i < σ.length := by omega
    by_cases hir : i < r'
    · rw [hS'lt i hir]
      have h3 := hR3 i hi' hmB
      have hle : policyMisses σ S i + 1 ≤ j0 := by
        have := policyMisses_succ σ S i
        rw [if_pos hmB] at this
        have := policyMisses_mono σ S (show i + 1 ≤ r' by omega)
        omega
      show _ = if _ ≤ j0 then _ else _
      rw [if_pos hle, h3]
    · have hc := hcardS' i (by omega) (le_of_lt hi')
      have hge := hj0le i (by omega)
      show _ = if _ ≤ j0 then _ else _
      rw [if_neg (by omega)]
      omega
  have hlegal : IsLegal m' (σ.take r) S' := by
    refine ⟨?_, ?_⟩
    · by_cases h0 : 0 < r'
      · rw [hS'lt 0 h0]; exact hS.1
      · rw [hS'ge 0 (by omega)]
        have : r' = 0 := by omega
        ext x
        simp only [Finset.mem_union, Finset.notMem_empty, iff_false]
        rintro (h | h)
        · rw [this, hS.1] at h; simp at h
        · rw [mem_loadedIn] at h
          obtain ⟨t, h1, h2, _⟩ := h
          omega
    · intro i hi
      have hi' : i < r := by rw [hlen] at hi; exact hi
      have hiσ : i < σ.length := by omega
      have hget : (σ.take r)[i] = σ[i] := List.getElem_take
      rw [hget]
      refine ⟨?_, ?_⟩
      · by_cases h1 : i + 1 < r'
        · rw [hS'lt (i + 1) h1, hS'lt i (by omega)]
          exact (hS.2 i hiσ).1
        · by_cases h2 : i < r'
          · have heq : i + 1 = r' := by omega
            rw [hS'ge (i + 1) (by omega), hS'lt i h2]
            intro x hx
            rw [Finset.mem_union] at hx
            rcases hx with hx | hx
            · rw [← heq] at hx
              exact (hS.2 i hiσ).1 hx
            · rw [mem_loadedIn] at hx
              obtain ⟨t, a, b, _⟩ := hx
              omega
          · rw [hS'ge (i + 1) (by omega), hS'ge i (by omega)]
            intro x hx
            rw [Finset.mem_insert, Finset.mem_union]
            rw [Finset.mem_union] at hx
            rcases hx with hx | hx
            · exact Or.inr (Or.inl hx)
            · rw [mem_loadedIn] at hx
              obtain ⟨t, a, b, c, d⟩ := hx
              rcases Nat.lt_succ_iff_lt_or_eq.1 b with h | h
              · right; right
                rw [mem_loadedIn]
                exact ⟨t, a, h, c, d⟩
              · subst h
                rw [List.getElem?_eq_getElem hiσ, Option.some.injEq] at d
                exact Or.inl d.symm
      · intro hnot
        have hmB : missB (σ.take r) S' i = true := by
          rw [hmissEq i hi', missB_iff σ S hiσ]
          exact fun h => hnot ((hmemEq i hiσ).2 h)
        have := hR3' i hi hmB
        omega
  have hcold' : AllMissesCold (σ.take r) S' := by
    intro i hi hmB
    rw [hlen] at hi
    rw [hmissEq i hi] at hmB
    obtain ⟨hi2, hni⟩ := hR2 i (by omega) hmB
    refine ⟨by rw [hlen]; exact hi, ?_⟩
    have hget : (σ.take r)[i] = σ[i] := List.getElem_take
    rw [hget]
    have htt : (σ.take r).take i = σ.take i := by
      rw [List.take_take, Nat.min_eq_left (by omega)]
    rw [htt]
    exact hni
  have hR1' : LRUAlwaysMisses (augCap 2 3 m') (σ.take r) := by
    intro i hi
    have hi' : i < r := by rw [hlen] at hi; exact hi
    have hget : (σ.take r)[i] = σ[i] := List.getElem_take
    rw [hget]
    have htt : (σ.take r).take i = σ.take i := by
      rw [List.take_take, Nat.min_eq_left (by omega)]
    rw [htt, hlru i (by omega)]
    exact hR1 i (by omega)
  have hprof : IsMemoryProfile m' := by
    refine ⟨?_, ?_⟩
    · intro j
      show 1 ≤ if j ≤ j0 then m j else (S r').card + (j - j0)
      split_ifs with h
      · exact hm.1 j
      · omega
    · intro j
      show (if j + 1 ≤ j0 then m (j + 1) else (S r').card + (j + 1 - j0)) ≤
        (if j ≤ j0 then m j else (S r').card + (j - j0)) + 1
      by_cases h1 : j + 1 ≤ j0
      · rw [if_pos h1, if_pos (by omega)]
        exact hm.2 j
      · rw [if_neg h1]
        by_cases h2 : j ≤ j0
        · rw [if_pos h2]
          have hj : j = j0 := by omega
          have hcap := card_cap m σ S hS r' (by omega)
          rw [← hj0] at hcap
          rw [hj]
          split_ifs at hcap with hz
          · omega
          · omega
        · rw [if_neg h2]
          omega
  have hopt' : IsOptimal m' (σ.take r) S' := by
    refine ⟨hlegal, ?_⟩
    have := ChangingCache.UpperBound.observation_3_1 m' (σ.take r) S' hlegal hcold'
      (σ.take r).length le_rfl
    rwa [List.take_length] at this
  refine ⟨m', S', ⟨hprof, hopt', hR1', hcold', hR3'⟩, hm'eq, ?_, hmissEq, ?_, ?_⟩
  · intro u hu
    rw [hlru u hu]
  · intro u h1 _
    exact hS'ge u h1
  · intro u h1 h2
    refine ⟨?_, ?_, ?_⟩
    · unfold bank3 lruMissCount
      have htt : (σ.take r).take u = σ.take u := by
        rw [List.take_take, Nat.min_eq_left h2]
      rw [hPM u h2, htt, hlru u h2]
    · intro x hx
      rw [hS'ge u h1]
      exact held m σ S hS r' u h1 (by omega) hx
    · have := hcardS' u h1 (by omega)
      omega
