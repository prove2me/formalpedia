-- Prove2me | solution 1 for BitcoinBackbone.common_prefix_private
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-29T15:21:17.107497+00:00
-- url     : https://prove2.me/submissions/aa209652-18f6-417a-aa7a-6c7cc1bfec98

import Definitions.Def_BitcoinBackbone

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

/-- Rounds are nondecreasing along a valid chain. -/
private theorem round_mono (E : Execution) (hE : E.Legal) (C : Chain) (hC : E.ValidChain C)
    (a b : ℕ) (hab : a ≤ b) (hb : b < C.length) : (C[a]'(by omega)).round ≤ C[b].round := by
  rcases Nat.eq_or_lt_of_le hab with rfl | hab
  · exact le_rfl
  have hmem : C[a] ∈ C.take b := by
    rw [List.mem_iff_getElem]
    exact ⟨a, by rw [List.length_take]; omega, by rw [List.getElem_take]⟩
  rcases hB : C[b] with ⟨q, s⟩ | ⟨s, j⟩
  · obtain ⟨hq, -, htake⟩ := valid_honest_at E C hC b hb q s hB
    rw [htake] at hmem
    exact (hE.base_rounds q s hq _ hmem).le
  · obtain ⟨hj, htake⟩ := valid_adv_at E C hC b hb s j hB
    rw [htake] at hmem
    exact hE.advParent_rounds s j hj _ hmem

/-- A block occurs at most once in a valid chain (it determines its ancestry). -/
private theorem index_unique (E : Execution) (C : Chain) (hC : E.ValidChain C)
    (a b : ℕ) (ha : a < C.length) (hb : b < C.length) (h : C[a] = C[b]) : a = b := by
  rcases hB : C[b] with ⟨q, s⟩ | ⟨s, j⟩
  · rw [hB] at h
    have h1 := length_base_of_honest_at E C hC a ha q s h
    have h2 := length_base_of_honest_at E C hC b hb q s hB
    omega
  · rw [hB] at h
    have h1 := length_advParent_of_adv_at E C hC a ha s j h
    have h2 := length_advParent_of_adv_at E C hC b hb s j hB
    omega

/-- A valid chain contains at most one honest block per round. -/
private theorem honest_round_unique (E : Execution) (hE : E.Legal) (C : Chain)
    (hC : E.ValidChain C) (a b : ℕ) (ha : a < C.length) (hb : b < C.length)
    (q q' s : ℕ) (hA : C[a] = Block.honest q s) (hB : C[b] = Block.honest q' s) : a = b := by
  by_contra hne
  wlog hab : a < b generalizing a b q q'
  · exact this b a hb ha q' q hB hA (Ne.symm hne) (by omega)
  have hmem : C[a] ∈ C.take b := by
    rw [List.mem_iff_getElem]
    exact ⟨a, by rw [List.length_take]; omega, by rw [List.getElem_take]⟩
  obtain ⟨hq', -, htake⟩ := valid_honest_at E C hC b hb q' s hB
  rw [htake] at hmem
  have := hE.base_rounds q' s hq' _ hmem
  rw [hA] at this
  simp [Block.round] at this

/-- **Height uniqueness** (GKL, Lemma 14 of the full version): if round `i` is uniquely
successful with honest miner `m`, whose block has height `(base m i).length + 1`, then any honest
block at that height in any valid chain is that block. -/
private theorem height_unique (E : Execution) (hE : E.Legal) (i m : ℕ) (hm : m < E.n)
    (hmi : E.mined m i = true) (huniq : ∀ q, q < E.n → E.mined q i = true → q = m)
    (C : Chain) (hC : E.ValidChain C) (t : ℕ) (ht : t < C.length) (hti : t = (E.base m i).length)
    (q s : ℕ) (h : C[t] = Block.honest q s) : q = m ∧ s = i := by
  obtain ⟨hq, hqs, -⟩ := valid_honest_at E C hC t ht q s h
  have hlen := length_base_of_honest_at E C hC t ht q s h
  rcases lt_trichotomy s i with hsi | rfl | hsi
  · exfalso
    have h1 := length_chain_le_base E hE m q hm hq s i hsi
    have h2 := length_chain_of_mined E q s (mined_pos E hE q s hqs) hqs
    omega
  · exact ⟨huniq q hq hqs, rfl⟩
  · exfalso
    have h1 := length_chain_le_base E hE q m hq hm i s hsi
    have h2 := length_chain_of_mined E m i (mined_pos E hE m i hmi) hmi
    omega

/-- The heights of the blocks of two uniquely successful rounds differ. -/
private theorem height_strict_mono (E : Execution) (hE : E.Legal) (i i' m m' : ℕ) (hm : m < E.n)
    (hm' : m' < E.n) (hmi : E.mined m i = true) (hii' : i < i') :
    (E.base m i).length < (E.base m' i').length := by
  have h1 := length_chain_le_base E hE m' m hm' hm i i' hii'
  have h2 := length_chain_of_mined E m i (mined_pos E hE m i hmi) hmi
  omega

private theorem card_advBlocks (E : Execution) (a b : ℕ) :
    (E.advBlocks a b).card = ∑ i ∈ Finset.Icc a b, E.Z i := by
  unfold Execution.advBlocks
  rw [Finset.card_image_of_injective, Finset.card_sigma]
  · simp
  · rintro ⟨s, j⟩ ⟨s', j'⟩ h
    simp only [Block.adv.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl

private theorem mem_advBlocks (E : Execution) (a b s j : ℕ) (hj : j < E.Z s) (has : a ≤ s)
    (hsb : s ≤ b) : Block.adv s j ∈ E.advBlocks a b := by
  unfold Execution.advBlocks
  rw [Finset.mem_image]
  exact ⟨⟨s, j⟩, by rw [Finset.mem_sigma, Finset.mem_Icc, Finset.mem_range]; exact ⟨⟨has, hsb⟩, hj⟩,
    rfl⟩

/-- Distinct adversarial blocks of rounds `a, …, b` number at most `∑_{i=a}^{b} Z_i`. -/
private theorem card_le_sum_Z (E : Execution) (S : Finset ℕ) (g : ℕ → Block) (a b : ℕ)
    (hg : ∀ i ∈ S, ∃ s j, g i = Block.adv s j ∧ j < E.Z s ∧ a ≤ s ∧ s ≤ b)
    (hinj : Set.InjOn g S) : S.card ≤ ∑ i ∈ Finset.Icc a b, E.Z i := by
  rw [← card_advBlocks]
  refine Finset.card_le_card_of_injOn g ?_ hinj
  intro i hi
  obtain ⟨s, j, hgi, hj, has, hsb⟩ := hg i hi
  rw [hgi]
  exact mem_advBlocks E a b s j hj has hsb

/-- The adversarial blocks at indices `[i₀, j)` of a valid chain, all of rounds in `[a, b]`, number
at most `∑_{i=a}^{b} Z_i`. -/
private theorem run_le_sum_Z (E : Execution) (C : Chain) (hC : E.ValidChain C) (i₀ j a b : ℕ)
    (hj : j ≤ C.length)
    (hadv : ∀ k (hk : k < C.length), i₀ ≤ k → k < j →
      C[k].isHonest = false ∧ a ≤ C[k].round ∧ C[k].round ≤ b) :
    j - i₀ ≤ ∑ i ∈ Finset.Icc a b, E.Z i := by
  have := card_le_sum_Z E (Finset.Ico i₀ j) (fun k => C.getD k default) a b ?_ ?_
  · simpa using this
  · intro k hk
    rw [Finset.mem_Ico] at hk
    have hkC : k < C.length := by omega
    obtain ⟨h1, h2, h3⟩ := hadv k hkC hk.1 hk.2
    obtain ⟨s, j', hsj⟩ := (not_isHonest_iff _).1 h1
    rw [hsj] at h2 h3
    obtain ⟨hj', -⟩ := valid_adv_at E C hC k hkC s j' hsj
    refine ⟨s, j', ?_, hj', h2, h3⟩
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hkC, Option.getD_some]
    exact hsj
  · intro k hk k' hk' h
    simp only [Finset.coe_Ico, Set.mem_Ico] at hk hk'
    have hkC : k < C.length := by omega
    have hkC' : k' < C.length := by omega
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hkC,
      List.getElem?_eq_getElem hkC', Option.getD_some] at h
    exact index_unique E C hC k k' hkC hkC' h

private theorem sum_Ioo_eq_Ico (a b : ℕ) (f : ℕ → ℕ) :
    ∑ i ∈ Finset.Ioo a b, f i = ∑ i ∈ Finset.Ico (a + 1) b, f i := by
  have : Finset.Ioo a b = Finset.Ico (a + 1) b := by
    ext; simp only [Finset.mem_Ioo, Finset.mem_Ico]; omega
  rw [this]

private theorem typical_pos (E : Execution) (lam : ℕ) (hT : E.Typical lam) : 0 < lam := by
  by_contra h
  have := hT 0 0 (by omega)
  simp at this

private theorem sum_Y_le_card (E : Execution) (s : Finset ℕ) : ∑ i ∈ s, E.Y i ≤ s.card := by
  calc ∑ i ∈ s, E.Y i ≤ ∑ i ∈ s, 1 := Finset.sum_le_sum (fun i _ => Y_le_one E i)
    _ = s.card := by simp

/-- In a typical execution, the adversary finds fewer than `λ` blocks in any `λ + 1` consecutive
rounds (`∑_{i=a}^{b} Z_i ≤ λ - 2` whenever `b ≤ a + λ`). -/
private theorem sum_Z_short_window (E : Execution) (lam : ℕ) (hT : E.Typical lam) (a b : ℕ)
    (hb : b ≤ a + lam) : ∑ i ∈ Finset.Icc a b, E.Z i + 2 ≤ lam := by
  have h1 : ∑ i ∈ Finset.Icc a b, E.Z i ≤ ∑ i ∈ Finset.Icc a (a + lam), E.Z i :=
    Finset.sum_le_sum_of_subset (Finset.Icc_subset_Icc le_rfl hb)
  have h2 := hT a (a + lam) le_rfl
  have h3 := sum_Y_le_card E (Finset.Ioo a (a + lam))
  simp at h3
  omega

private theorem getD_eq (C : Chain) (k : ℕ) (hk : k < C.length) : C.getD k default = C[k] :=
  List.getD_eq_getElem C default hk

/-- A run of adversarial blocks `[i₀, j)` of a valid chain, bounded below by an honest chain of
round `r₁` of length `≥ i₀` and above by a chain adopted in round `r₂` of length `≤ j`, with all
its blocks of rounds in `[r₁, r₂]`, has fewer than `λ` blocks in a typical execution. -/
private theorem run_bound (E : Execution) (hE : E.Legal) (lam : ℕ) (hT : E.Typical lam)
    (C : Chain) (hC : E.ValidChain C) (i₀ j : ℕ) (hj : j ≤ C.length)
    (q m r₁ r₂ : ℕ) (hq : q < E.n) (hm : m < E.n)
    (hlow : i₀ ≤ (E.chain q r₁).length) (hup : (E.base m r₂).length ≤ j)
    (hadv : ∀ k (hk : k < C.length), i₀ ≤ k → k < j →
      C[k].isHonest = false ∧ r₁ ≤ C[k].round ∧ C[k].round ≤ r₂) :
    j < i₀ + lam := by
  have hcount := run_le_sum_Z E C hC i₀ j r₁ r₂ hj hadv
  have hlam := typical_pos E lam hT
  rcases Nat.lt_or_ge r₂ (r₁ + lam) with h | h
  · have := sum_Z_short_window E lam hT r₁ r₂ h.le
    omega
  · exfalso
    have h1 := growth_base E hE q hq r₁ r₂ (by omega) m hm
    have h2 := hT r₁ r₂ h
    have h3 : ∑ i ∈ Finset.Ioo r₁ r₂, E.Y i ≤ ∑ i ∈ Finset.Ico (r₁ + 1) r₂, E.X i := by
      rw [sum_Ioo_eq_Ico]
      exact Finset.sum_le_sum (fun i _ => Y_le_X E i)
    omega

/-- **Private-chain attack fails** (counting form of common prefix): let `C` be the chain of honest
party `p` at the end of round `r`, and `D` any valid chain of blocks of rounds `≤ r` whose block at
height `f` is an honest block of round `r₀` (or `f = 0`, the genesis, with `r₀ = 0`) and all of whose
blocks above height `f` are adversarial — e.g. `D = C.take f ++ (private adversarial blocks)`.
In a typical execution with `r₀ + λ ≤ r` the private chain is strictly shorter than `C`:
the honest blocks mined after the fork number at least `∑ X` over the window, the adversarial ones
at most `∑ Z`. -/
theorem solution (E : BitcoinBackbone.Execution) (hE : E.Legal)
    (lam : ℕ) (hT : E.Typical lam) (p : ℕ) (hp : p < E.n) (r : ℕ)
    (D : BitcoinBackbone.Chain) (hD : E.ValidChain D) (hDr : ∀ B ∈ D, B.round ≤ r)
    (f r₀ : ℕ) (hfD : f ≤ D.length)
    (hfork : (f = 0 ∧ r₀ = 0) ∨
      ∃ q, ∃ hf : f - 1 < D.length, 0 < f ∧ D[f - 1] = BitcoinBackbone.Block.honest q r₀)
    (hadv : ∀ k (hk : k < D.length), f ≤ k → D[k].isHonest = false)
    (hwin : r₀ + lam ≤ r) : D.length < (E.chain p r).length := by
  have hlam := typical_pos E lam hT
  obtain ⟨q, hq, hlenq, hround⟩ : ∃ q, q < E.n ∧ (E.chain q r₀).length = f ∧
      ∀ k (hk : k < D.length), f ≤ k → r₀ ≤ D[k].round := by
    rcases hfork with ⟨rfl, rfl⟩ | ⟨q, hf, hf0, hDf⟩
    · exact ⟨p, hp, by simp [Execution.chain], fun k hk _ => Nat.zero_le _⟩
    · obtain ⟨hqn, hqm, -⟩ := valid_honest_at E D hD (f - 1) hf q r₀ hDf
      have hlen := length_base_of_honest_at E D hD (f - 1) hf q r₀ hDf
      refine ⟨q, hqn, ?_, ?_⟩
      · rw [length_chain_of_mined E q r₀ (mined_pos E hE q r₀ hqm) hqm]; omega
      · intro k hk hfk
        have := round_mono E hE D hD (f - 1) k (by omega) hk
        rw [hDf] at this
        exact this
  have hcount := run_le_sum_Z E D hD f D.length r₀ r le_rfl
    (fun k hk h1 _ => ⟨hadv k hk h1, hround k hk h1, hDr _ (List.getElem_mem hk)⟩)
  have hgrow := growth_base E hE q hq r₀ r (by omega) p hp
  have hT' := hT r₀ r hwin
  have h3 : ∑ i ∈ Finset.Ioo r₀ r, E.Y i ≤ ∑ i ∈ Finset.Ico (r₀ + 1) r, E.X i := by
    rw [sum_Ioo_eq_Ico]
    exact Finset.sum_le_sum (fun i _ => Y_le_X E i)
  have h4 := length_base_le_chain E p r (by omega)
  omega
