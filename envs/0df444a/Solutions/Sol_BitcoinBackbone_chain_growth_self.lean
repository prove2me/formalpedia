-- Prove2me | solution 1 for BitcoinBackbone.chain_growth_self
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-29T15:23:19.702583+00:00
-- url     : https://prove2.me/submissions/87d72252-0f31-4c8a-8338-05f9b4ff9cfe

import Definitions.Def_BitcoinBackbone
import Theorems.Thm_BitcoinBackbone_chain_growth

open BitcoinBackbone

private theorem round_honest (p r : ℕ) : (Block.honest p r).round = r := rfl

private theorem round_adv (r j : ℕ) : (Block.adv r j).round = r := rfl

private theorem isHonest_iff (B : Block) : B.isHonest = true ↔ ∃ p r, B = Block.honest p r := by
  cases B <;> simp [Block.isHonest]

private theorem not_isHonest_iff (B : Block) : B.isHonest = false ↔ ∃ r j, B = Block.adv r j := by
  cases B <;> simp [Block.isHonest]

/-- The chain of an honest party that mined in round `r ≥ 1`. -/
private theorem chain_of_mined (E : Execution) (p r : ℕ) (hr : 1 ≤ r) (h : E.mined p r = true) :
    E.chain p r = E.base p r ++ [Block.honest p r] := by
  obtain ⟨r, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  simp [Execution.chain, h]

private theorem chain_of_not_mined (E : Execution) (p r : ℕ) (hr : 1 ≤ r)
    (h : E.mined p r = false) : E.chain p r = E.base p r := by
  obtain ⟨r, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  simp [Execution.chain, h]

private theorem base_prefix_chain (E : Execution) (p r : ℕ) (hr : 1 ≤ r) :
    E.base p r <+: E.chain p r := by
  cases h : E.mined p r
  · rw [chain_of_not_mined E p r hr h]
  · rw [chain_of_mined E p r hr h]; exact List.prefix_append _ _

private theorem length_base_le_chain (E : Execution) (p r : ℕ) (hr : 1 ≤ r) :
    (E.base p r).length ≤ (E.chain p r).length :=
  (base_prefix_chain E p r hr).length_le

private theorem length_chain_of_mined (E : Execution) (p r : ℕ) (hr : 1 ≤ r)
    (h : E.mined p r = true) : (E.chain p r).length = (E.base p r).length + 1 := by
  rw [chain_of_mined E p r hr h]; simp

/-- Validity of a chain extended by one block. -/
private theorem validChain_append (E : Execution) (C : Chain) (B : Block)
    (hC : E.ValidChain C) (hB : E.Extends C B) : E.ValidChain (C ++ [B]) := by
  intro i hi
  simp only [List.length_append, List.length_singleton] at hi
  rcases Nat.lt_or_ge i C.length with h | h
  · rw [List.getElem_append_left h, List.take_append_of_le_length h.le]
    exact hC i h
  · have hi' : i = C.length := by omega
    subst hi'
    rw [List.getElem_append_right (le_refl _), List.take_append_of_le_length (le_refl _),
      List.take_length]
    simpa using hB

private theorem chain_valid (E : Execution) (hE : E.Legal) (p : ℕ) (hp : p < E.n) (r : ℕ) :
    E.ValidChain (E.chain p r) := by
  cases r with
  | zero => intro i hi; simp [Execution.chain] at hi
  | succ r =>
    cases h : E.mined p (r + 1)
    · rw [chain_of_not_mined E p (r + 1) (by omega) h]
      exact hE.base_valid p (r + 1) hp (by omega)
    · rw [chain_of_mined E p (r + 1) (by omega) h]
      exact validChain_append E _ _ (hE.base_valid p (r + 1) hp (by omega))
        ⟨hp, h, rfl⟩

private theorem chain_rounds (E : Execution) (hE : E.Legal) (p : ℕ) (hp : p < E.n) (r : ℕ) :
    ∀ B ∈ E.chain p r, B.round ≤ r := by
  intro B hB
  cases r with
  | zero => simp [Execution.chain] at hB
  | succ r =>
    cases h : E.mined p (r + 1)
    · rw [chain_of_not_mined E p (r + 1) (by omega) h] at hB
      exact (hE.base_rounds p (r + 1) hp B hB).le
    · rw [chain_of_mined E p (r + 1) (by omega) h, List.mem_append, List.mem_singleton] at hB
      rcases hB with hB | rfl
      · exact (hE.base_rounds p (r + 1) hp B hB).le
      · simp [Block.round]

/-- Validity of a chain, read at an index holding an honest block. -/
private theorem valid_honest_at (E : Execution) (C : Chain) (hC : E.ValidChain C) (t : ℕ)
    (ht : t < C.length) (q s : ℕ) (h : C[t] = Block.honest q s) :
    q < E.n ∧ E.mined q s = true ∧ C.take t = E.base q s := by
  have := hC t ht
  rw [h] at this
  exact this

private theorem valid_adv_at (E : Execution) (C : Chain) (hC : E.ValidChain C) (t : ℕ)
    (ht : t < C.length) (s j : ℕ) (h : C[t] = Block.adv s j) :
    j < E.Z s ∧ C.take t = E.advParent s j := by
  have := hC t ht
  rw [h] at this
  exact this

/-- An honest block at index `t` of a valid chain was mined on a chain of length `t`. -/
private theorem length_base_of_honest_at (E : Execution) (C : Chain) (hC : E.ValidChain C) (t : ℕ)
    (ht : t < C.length) (q s : ℕ) (h : C[t] = Block.honest q s) :
    (E.base q s).length = t := by
  have := (valid_honest_at E C hC t ht q s h).2.2
  rw [← this, List.length_take]; omega

private theorem length_advParent_of_adv_at (E : Execution) (C : Chain) (hC : E.ValidChain C) (t : ℕ)
    (ht : t < C.length) (s j : ℕ) (h : C[t] = Block.adv s j) :
    (E.advParent s j).length = t := by
  have := (valid_adv_at E C hC t ht s j h).2
  rw [← this, List.length_take]; omega

private theorem mined_pos (E : Execution) (hE : E.Legal) (q s : ℕ) (h : E.mined q s = true) :
    1 ≤ s := by
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · rw [hE.mined_zero] at h; exact absurd h (by simp)
  · exact hs

/-- Any honest chain of round `i < s` is at most as long as what any honest party adopts in
round `s`. -/
private theorem length_chain_le_base (E : Execution) (hE : E.Legal) (p q : ℕ) (hp : p < E.n)
    (hq : q < E.n) (i s : ℕ) (his : i < s) : (E.chain q i).length ≤ (E.base p s).length := by
  induction s with
  | zero => omega
  | succ s ih =>
    rcases Nat.lt_or_ge i s with h | h
    · exact (ih h).trans ((length_base_le_chain E p s (by omega)).trans
        (hE.base_length p p s hp hp))
    · have : i = s := by omega
      subst this
      exact hE.base_length p q i hp hq

/-- The honest-count predicates. -/
private theorem X_eq_one_iff (E : Execution) (r : ℕ) :
    E.X r = 1 ↔ ∃ m, m < E.n ∧ E.mined m r = true := by
  unfold Execution.X Execution.honestCount
  constructor
  · intro h
    split_ifs at h with hc
    · rw [Finset.card_pos] at hc
      obtain ⟨m, hm⟩ := hc
      rw [Finset.mem_filter, Finset.mem_range] at hm
      exact ⟨m, hm.1, hm.2⟩
  · rintro ⟨m, hm, hmr⟩
    have : 0 < ((Finset.range E.n).filter (fun p => E.mined p r = true)).card := by
      rw [Finset.card_pos]
      exact ⟨m, by rw [Finset.mem_filter, Finset.mem_range]; exact ⟨hm, hmr⟩⟩
    simp [this]

private theorem X_le_one (E : Execution) (r : ℕ) : E.X r ≤ 1 := by
  unfold Execution.X; split_ifs <;> omega

private theorem Y_le_X (E : Execution) (r : ℕ) : E.Y r ≤ E.X r := by
  unfold Execution.X Execution.Y; split_ifs <;> omega

private theorem Y_le_one (E : Execution) (r : ℕ) : E.Y r ≤ 1 := by
  unfold Execution.Y; split_ifs <;> omega

/-- A uniquely successful round has exactly one honest miner. -/
private theorem Y_eq_one_iff (E : Execution) (r : ℕ) :
    E.Y r = 1 ↔ ∃ m, m < E.n ∧ E.mined m r = true ∧
      ∀ q, q < E.n → E.mined q r = true → q = m := by
  unfold Execution.Y Execution.honestCount
  constructor
  · intro h
    split_ifs at h with hc
    · rw [Finset.card_eq_one] at hc
      obtain ⟨m, hm⟩ := hc
      have hmem : ∀ q, q ∈ (Finset.range E.n).filter (fun p => E.mined p r = true) ↔ q = m := by
        intro q; rw [hm, Finset.mem_singleton]
      have hm' := (hmem m).2 rfl
      rw [Finset.mem_filter, Finset.mem_range] at hm'
      refine ⟨m, hm'.1, hm'.2, fun q hq hqr => (hmem q).1 ?_⟩
      rw [Finset.mem_filter, Finset.mem_range]; exact ⟨hq, hqr⟩
  · rintro ⟨m, hm, hmr, huniq⟩
    have : (Finset.range E.n).filter (fun p => E.mined p r = true) = {m} := by
      ext q
      rw [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
      constructor
      · rintro ⟨hq, hqr⟩; exact huniq q hq hqr
      · rintro rfl; exact ⟨hm, hmr⟩
    simp [this]

/-- Core of chain growth: what any honest party adopts in round `s > r` is at least as long as
any honest chain of round `r` plus the number of successful rounds strictly between. -/
private theorem growth_base (E : Execution) (hE : E.Legal) (p : ℕ) (hp : p < E.n)
    (r s : ℕ) (hrs : r < s) : ∀ q, q < E.n →
    (E.chain p r).length + ∑ i ∈ Finset.Ico (r + 1) s, E.X i ≤ (E.base q s).length := by
  induction s with
  | zero => omega
  | succ s ih =>
    intro q hq
    rcases Nat.lt_or_ge r s with h | h
    · rw [Finset.sum_Ico_succ_top (by omega)]
      rcases Nat.eq_zero_or_pos (E.X s) with hX | hX
      · rw [hX, add_zero]
        exact (ih h q hq).trans ((length_base_le_chain E q s (by omega)).trans
          (hE.base_length q q s hq hq))
      · have hX1 : E.X s = 1 := by have := X_le_one E s; omega
        obtain ⟨m, hm, hms⟩ := (X_eq_one_iff E s).1 hX1
        rw [hX1]
        have h1 := ih h m hm
        have h2 : (E.chain m s).length = (E.base m s).length + 1 :=
          length_chain_of_mined E m s (by omega) hms
        have h3 := hE.base_length q m s hq hm
        omega
    · have : r = s := by omega
      subst this
      simp
      exact hE.base_length q p r hq hp

/-- Chain growth for a single party, over any `r ≤ s`. -/
theorem solution (E : BitcoinBackbone.Execution) (hE : E.Legal)
    (p : ℕ) (hp : p < E.n) (r s : ℕ) (hrs : r ≤ s) :
    (E.chain p r).length + ∑ i ∈ Finset.Ico (r + 1) s, E.X i ≤ (E.chain p s).length := by
  rcases Nat.lt_or_ge r s with h | h
  · exact BitcoinBackbone.chain_growth E hE p p hp hp r s h
  · have : r = s := by omega
    subst this; simp
