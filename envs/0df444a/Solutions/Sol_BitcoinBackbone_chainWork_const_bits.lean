-- Prove2me | solution 1 for BitcoinBackbone.chainWork_const_bits
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-29T15:21:15.440895+00:00
-- url     : https://prove2.me/submissions/c8575416-e67c-495e-a0d3-76030d29b282

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

/-- The round of the last honest block among the first `L` blocks of `C` (`0` if there is none). -/
private def lastHonestRound (C : Chain) (L : ℕ) : ℕ :=
  ((Finset.range L).filter (fun t => (C.getD t default).isHonest = true)).sup
    (fun t => (C.getD t default).round)

private theorem le_lastHonestRound (C : Chain) (L t : ℕ) (htL : t < L) (ht : t < C.length)
    (q s : ℕ) (h : C[t] = Block.honest q s) : s ≤ lastHonestRound C L := by
  unfold lastHonestRound
  have hmem : t ∈ (Finset.range L).filter (fun t => (C.getD t default).isHonest = true) := by
    rw [Finset.mem_filter, Finset.mem_range, getD_eq C t ht, h]
    exact ⟨htL, rfl⟩
  have h1 : s = (fun t => (C.getD t default).round) t := by
    simp only [getD_eq C t ht, h]; rfl
  rw [h1]
  exact Finset.le_sup (f := fun t => (C.getD t default).round) hmem

private theorem lastHonestRound_spec (C : Chain) (L : ℕ) :
    lastHonestRound C L = 0 ∨
      ∃ t, t < L ∧ ∃ ht : t < C.length, ∃ q, C[t] = Block.honest q (lastHonestRound C L) := by
  classical
  by_cases hne : ((Finset.range L).filter (fun t => (C.getD t default).isHonest = true)).Nonempty
  · right
    obtain ⟨t, ht, hsup⟩ := Finset.exists_mem_eq_sup _ hne (fun t => (C.getD t default).round)
    rw [Finset.mem_filter, Finset.mem_range] at ht
    have htC : t < C.length := by
      by_contra hcon
      push Not at hcon
      rw [List.getD_eq_default _ _ hcon] at ht
      simp [Block.isHonest] at ht
    rw [getD_eq C t htC] at ht
    obtain ⟨q, s, hqs⟩ := (isHonest_iff _).1 ht.2
    refine ⟨t, ht.1, htC, q, ?_⟩
    unfold lastHonestRound
    rw [hsup, getD_eq C t htC, hqs]
    rfl
  · left
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    unfold lastHonestRound
    rw [hne, Finset.sup_empty]
    rfl

/-- **The pairing argument** (GKL, proof of Lemma 15): let `C₁` be the chain of honest party `p`
at the end of round `r`, `C₂` a valid chain of blocks of rounds `≤ r` at least as long as `C₁`,
`L` the length of their longest common prefix, and `r*` the round of the last honest block in that
prefix.  Every uniquely successful round in `(r*, r)` is matched with a distinct adversarial block
of a round in `[r*, r]`, so `∑_{(r*, r)} Y ≤ ∑_{[r*, r]} Z`.  In a typical execution this forces
`r* + λ > r`. -/
private theorem pairing_core (E : Execution) (hE : E.Legal) (lam : ℕ) (hT : E.Typical lam)
    (p : ℕ) (hp : p < E.n) (r : ℕ) (C₂ : Chain) (hC₂ : E.ValidChain C₂)
    (hC₂r : ∀ B ∈ C₂, B.round ≤ r) (hlen : (E.chain p r).length ≤ C₂.length)
    (L : ℕ) (hL : L ≤ (E.chain p r).length) (hagree : (E.chain p r).take L = C₂.take L)
    (hmax : ∀ ℓ, ℓ ≤ (E.chain p r).length → (E.chain p r).take ℓ = C₂.take ℓ → ℓ ≤ L)
    (hwin : lastHonestRound (E.chain p r) L + lam ≤ r) : False := by
  classical
  set C₁ := E.chain p r with hC₁def
  have hC₁ : E.ValidChain C₁ := chain_valid E hE p hp r
  have hC₁r : ∀ B ∈ C₁, B.round ≤ r := chain_rounds E hE p hp r
  set rs := lastHonestRound C₁ L with hrs
  have hT' := hT rs r hwin
  have hcard : ∑ i ∈ Finset.Ioo rs r, E.Y i =
      ((Finset.Ioo rs r).filter (fun i => E.honestCount i = 1)).card := by
    rw [Finset.card_filter]
    rfl
  rw [hcard] at hT'
  -- agreement of the two chains below `L`
  have hagreeIdx : ∀ t, t < L → ∀ (h₁ : t < C₁.length) (h₂ : t < C₂.length), C₂[t] = C₁[t] := by
    intro t htL h₁ h₂
    have e1 : (C₁.take L)[t]'(by rw [List.length_take]; omega) = C₁[t] := List.getElem_take
    have e2 : (C₂.take L)[t]'(by rw [List.length_take]; omega) = C₂[t] := List.getElem_take
    rw [← e1, ← e2]
    simp only [hagree]
  -- one adversarial block per uniquely successful round
  have hclaim : ∀ i ∈ (Finset.Ioo rs r).filter (fun i => E.honestCount i = 1), ∃ B : Block,
      (∃ s j, B = Block.adv s j ∧ j < E.Z s ∧ rs ≤ s ∧ s ≤ r) ∧
      ∃ m, m < E.n ∧ E.mined m i = true ∧ ∃ C, (C = C₁ ∨ C = C₂) ∧
        ∃ h : (E.base m i).length < C.length, C[(E.base m i).length] = B := by
    intro i hi
    rw [Finset.mem_filter, Finset.mem_Ioo] at hi
    obtain ⟨⟨hrsi, hir⟩, hcount⟩ := hi
    have hY : E.Y i = 1 := by unfold Execution.Y; simp [hcount]
    obtain ⟨m, hm, hmi, huniq⟩ := (Y_eq_one_iff E i).1 hY
    set t := (E.base m i).length with htdef
    have ht₁ : t < C₁.length := by
      have h1 := length_chain_le_base E hE p m hp hm i r hir
      have h2 := length_chain_of_mined E m i (mined_pos E hE m i hmi) hmi
      have h3 : (E.base p r).length ≤ C₁.length := length_base_le_chain E p r (by omega)
      omega
    have ht₂ : t < C₂.length := by omega
    -- the block of round `i` is not in the common prefix
    have hnotboth : ¬ (C₁[t] = Block.honest m i ∧ C₂[t] = Block.honest m i) := by
      rintro ⟨h1, h2⟩
      have e1 := (valid_honest_at E C₁ hC₁ t ht₁ m i h1).2.2
      have e2 := (valid_honest_at E C₂ hC₂ t ht₂ m i h2).2.2
      have : C₁.take (t + 1) = C₂.take (t + 1) := by
        rw [List.take_succ_eq_append_getElem ht₁, List.take_succ_eq_append_getElem ht₂, e1, e2, h1, h2]
      have hle := hmax (t + 1) (by omega) this
      have := le_lastHonestRound C₁ L t (by omega) ht₁ m i h1
      rw [← hrs] at this
      omega
    obtain ⟨C, hC, hCv, hCr, hCagree, htC, hCt⟩ : ∃ C, (C = C₁ ∨ C = C₂) ∧ E.ValidChain C ∧
        (∀ B ∈ C, B.round ≤ r) ∧
        (∀ t', t' < L → ∀ (h₁ : t' < C₁.length) (h₂ : t' < C.length), C[t'] = C₁[t']) ∧
        ∃ h : t < C.length, C[t] ≠ Block.honest m i := by
      by_cases h1 : C₁[t] = Block.honest m i
      · exact ⟨C₂, Or.inr rfl, hC₂, hC₂r, hagreeIdx, ht₂, fun h2 => hnotboth ⟨h1, h2⟩⟩
      · exact ⟨C₁, Or.inl rfl, hC₁, hC₁r, fun _ _ _ _ => rfl, ht₁, h1⟩
    -- that block is adversarial (height uniqueness)
    obtain ⟨s, j, hsj⟩ : ∃ s j, C[t] = Block.adv s j := by
      rcases hB : C[t] with ⟨q, s'⟩ | ⟨s, j⟩
      · exfalso
        obtain ⟨rfl, rfl⟩ := height_unique E hE i m hm hmi huniq C hCv t htC rfl q s' hB
        exact hCt hB
      · exact ⟨s, j, rfl⟩
    obtain ⟨hj, htake⟩ := valid_adv_at E C hCv t htC s j hsj
    refine ⟨Block.adv s j, ⟨s, j, rfl, hj, ?_, ?_⟩, m, hm, hmi, C, hC, htC, hsj⟩
    · -- the adversarial block is above the last honest common block, hence of round ≥ r*
      rcases lastHonestRound_spec C₁ L with h0 | ⟨t', ht'L, ht'C, q, hq⟩
      · rw [hrs, h0]; exact Nat.zero_le _
      · rw [← hrs] at hq
        obtain ⟨hqn, hqm, -⟩ := valid_honest_at E C₁ hC₁ t' ht'C q rs hq
        have hlt : (E.base q rs).length < (E.base m i).length :=
          height_strict_mono E hE rs i q m hqn hm hqm hrsi
        have hlen' := length_base_of_honest_at E C₁ hC₁ t' ht'C q rs hq
        have ht'C' : t' < C.length := by omega
        have hmem : C[t'] ∈ C.take t := by
          rw [List.mem_iff_getElem]
          exact ⟨t', by rw [List.length_take]; omega, by rw [List.getElem_take]⟩
        rw [htake] at hmem
        have := hE.advParent_rounds s j hj _ hmem
        rw [hCagree t' ht'L ht'C ht'C', hq] at this
        exact this
    · have := hCr _ (List.getElem_mem htC)
      rw [hsj] at this
      exact this
  choose! g hg using hclaim
  have hinj : Set.InjOn g ((Finset.Ioo rs r).filter (fun i => E.honestCount i = 1)) := by
    intro i hi i' hi' heq
    have hi₀ : i ∈ (Finset.Ioo rs r).filter (fun i => E.honestCount i = 1) := hi
    have hi₀' : i' ∈ (Finset.Ioo rs r).filter (fun i => E.honestCount i = 1) := hi'
    obtain ⟨⟨s, j, hsj, -⟩, m, hm, hmi, C, hC, ht, hCt⟩ := hg i hi₀
    obtain ⟨-, m', hm', hmi', C', hC', ht', hCt'⟩ := hg i' hi₀'
    have hCv : E.ValidChain C := by rcases hC with rfl | rfl; exacts [hC₁, hC₂]
    have hCv' : E.ValidChain C' := by rcases hC' with rfl | rfl; exacts [hC₁, hC₂]
    have e1 := length_advParent_of_adv_at E C hCv _ ht s j (hCt.trans hsj)
    have e2 := length_advParent_of_adv_at E C' hCv' _ ht' s j (hCt'.trans (heq.symm.trans hsj))
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have := height_strict_mono E hE i i' m m' hm hm' hmi h; omega
    · have := height_strict_mono E hE i' i m' m hm' hm hmi' h; omega
  have := card_le_sum_Z E _ g rs r (fun i hi => (hg i hi).1) hinj
  omega

private theorem round_le_of_mem_upTo (C : Chain) (t : ℕ) (B : Block) (h : B ∈ C.upTo t) :
    B.round ≤ t := by
  have := List.mem_takeWhile_imp h
  simpa using this

private theorem upTo_prefix (C : Chain) (t : ℕ) : C.upTo t <+: C := List.takeWhile_prefix _

private theorem upTo_eq_take (C : Chain) (t : ℕ) : C.upTo t = C.take (C.upTo t).length :=
  List.prefix_iff_eq_take.1 (upTo_prefix C t)

/-- A prefix made of blocks of rounds `≤ t` is a prefix of `upTo t`. -/
private theorem prefix_upTo_of_prefix (C D : Chain) (t : ℕ) (h : D <+: C)
    (hD : ∀ B ∈ D, B.round ≤ t) : D <+: C.upTo t := by
  obtain ⟨rest, rfl⟩ := h
  unfold Chain.upTo
  have hself : D.takeWhile (fun B => decide (B.round ≤ t)) = D :=
    List.takeWhile_eq_self_iff.2 (fun B hB => by simpa using hD B hB)
  rw [List.takeWhile_append, hself]
  simp

/-- **Common prefix at a single round** (GKL, Lemma 15): `C₁` the chain of an honest party at the
end of round `r`, `C₂` any valid chain of blocks of rounds `≤ r` (another honest chain, or a chain
delivered by the adversary) at least as long as `C₁`; in a typical execution the blocks of either
chain older than `w ≥ λ` rounds form a prefix of the other. -/
private theorem same_round (E : Execution) (hE : E.Legal) (lam : ℕ) (hT : E.Typical lam)
    (p : ℕ) (hp : p < E.n) (r w : ℕ) (hw : lam ≤ w) (hwr : w ≤ r)
    (C₂ : Chain) (hC₂ : E.ValidChain C₂) (hC₂r : ∀ B ∈ C₂, B.round ≤ r)
    (hlen : (E.chain p r).length ≤ C₂.length) :
    (E.chain p r).upTo (r - w) <+: C₂ ∧ C₂.upTo (r - w) <+: E.chain p r := by
  classical
  set C₁ := E.chain p r with hC₁def
  have hC₁ : E.ValidChain C₁ := chain_valid E hE p hp r
  constructor
  · by_contra hnot
    set T := C₁.upTo (r - w) with hT_def
    have hTpre : T <+: C₁ := upTo_prefix _ _
    have hTtake : T = C₁.take T.length := upTo_eq_take _ _
    have hT1 : 1 ≤ T.length := by
      by_contra h0
      push Not at h0
      have : T = [] := List.length_eq_zero_iff.1 (by omega)
      exact hnot (this ▸ List.nil_prefix)
    have hex : ∃ ℓ, ¬ (C₁.take (ℓ + 1) <+: C₂) := by
      refine ⟨T.length - 1, ?_⟩
      rw [show T.length - 1 + 1 = T.length by omega, ← hTtake]; exact hnot
    set L := Nat.find hex with hLdef
    have hL1 : ¬ (C₁.take (L + 1) <+: C₂) := Nat.find_spec hex
    have hL2 : ∀ ℓ, ℓ < L → C₁.take (ℓ + 1) <+: C₂ := fun ℓ hℓ => by
      have := Nat.find_min hex hℓ
      push Not at this
      exact this
    have hLT : L + 1 ≤ T.length := by
      by_contra h
      push Not at h
      have := hL2 (T.length - 1) (by omega)
      rw [show T.length - 1 + 1 = T.length by omega, ← hTtake] at this
      exact hnot this
    have hLC : L < C₁.length := by have := hTpre.length_le; omega
    have hagreeL : C₁.take L <+: C₂ := by
      rcases Nat.eq_zero_or_pos L with h | h
      · rw [h]; simp
      · have := hL2 (L - 1) (by omega)
        rwa [show L - 1 + 1 = L by omega] at this
    have hagree : C₁.take L = C₂.take L := by
      have := List.prefix_iff_eq_take.1 hagreeL
      rwa [List.length_take, min_eq_left hLC.le] at this
    have hmax : ∀ ℓ, ℓ ≤ C₁.length → C₁.take ℓ = C₂.take ℓ → ℓ ≤ L := by
      intro ℓ _ hℓ
      by_contra h
      push Not at h
      apply hL1
      exact (List.take_prefix_take_left (by omega : L + 1 ≤ ℓ)).trans (hℓ ▸ List.take_prefix _ _)
    have hroundL : C₁[L].round ≤ r - w := by
      have hmem : C₁[L] ∈ T := by
        rw [← hTpre.getElem (by omega : L < T.length)]; exact List.getElem_mem _
      exact round_le_of_mem_upTo _ _ _ hmem
    have hrs : lastHonestRound C₁ L ≤ C₁[L].round := by
      rcases lastHonestRound_spec C₁ L with h0 | ⟨t, htL, htC, q, hq⟩
      · rw [h0]; exact Nat.zero_le _
      · have := round_mono E hE C₁ hC₁ t L htL.le hLC
        rw [hq] at this; exact this
    exact pairing_core E hE lam hT p hp r C₂ hC₂ hC₂r hlen L hLC.le hagree hmax
      (by show lastHonestRound C₁ L + lam ≤ r; omega)
  · by_contra hnot
    set T := C₂.upTo (r - w) with hT_def
    have hTpre : T <+: C₂ := upTo_prefix _ _
    have hTtake : T = C₂.take T.length := upTo_eq_take _ _
    have hT1 : 1 ≤ T.length := by
      by_contra h0
      push Not at h0
      have : T = [] := List.length_eq_zero_iff.1 (by omega)
      exact hnot (this ▸ List.nil_prefix)
    have hex : ∃ ℓ, ¬ (C₂.take (ℓ + 1) <+: C₁) := by
      refine ⟨T.length - 1, ?_⟩
      rw [show T.length - 1 + 1 = T.length by omega, ← hTtake]; exact hnot
    set L := Nat.find hex with hLdef
    have hL1 : ¬ (C₂.take (L + 1) <+: C₁) := Nat.find_spec hex
    have hL2 : ∀ ℓ, ℓ < L → C₂.take (ℓ + 1) <+: C₁ := fun ℓ hℓ => by
      have := Nat.find_min hex hℓ
      push Not at this
      exact this
    have hLT : L + 1 ≤ T.length := by
      by_contra h
      push Not at h
      have := hL2 (T.length - 1) (by omega)
      rw [show T.length - 1 + 1 = T.length by omega, ← hTtake] at this
      exact hnot this
    have hLC₂ : L < C₂.length := by have := hTpre.length_le; omega
    have hagreeL : C₂.take L <+: C₁ := by
      rcases Nat.eq_zero_or_pos L with h | h
      · rw [h]; simp
      · have := hL2 (L - 1) (by omega)
        rwa [show L - 1 + 1 = L by omega] at this
    have hLC₁ : L ≤ C₁.length := by
      have := hagreeL.length_le
      rw [List.length_take] at this; omega
    have hagree : C₁.take L = C₂.take L := by
      have := List.prefix_iff_eq_take.1 hagreeL
      rw [List.length_take, min_eq_left hLC₂.le] at this
      exact this.symm
    have hmax : ∀ ℓ, ℓ ≤ C₁.length → C₁.take ℓ = C₂.take ℓ → ℓ ≤ L := by
      intro ℓ _ hℓ
      by_contra h
      push Not at h
      apply hL1
      exact (List.take_prefix_take_left (by omega : L + 1 ≤ ℓ)).trans
        (hℓ.symm ▸ List.take_prefix _ _)
    have hroundL : C₂[L].round ≤ r - w := by
      have hmem : C₂[L] ∈ T := by
        rw [← hTpre.getElem (by omega : L < T.length)]; exact List.getElem_mem _
      exact round_le_of_mem_upTo _ _ _ hmem
    have hrs : lastHonestRound C₁ L ≤ C₂[L].round := by
      rcases lastHonestRound_spec C₁ L with h0 | ⟨t, htL, htC, q, hq⟩
      · rw [h0]; exact Nat.zero_le _
      · have h2 := round_mono E hE C₂ hC₂ t L htL.le hLC₂
        have e1 : (C₁.take L)[t]'(by rw [List.length_take]; omega) = C₁[t] := List.getElem_take
        have e2 : (C₂.take L)[t]'(by rw [List.length_take]; omega) = C₂[t] := List.getElem_take
        have : C₂[t] = C₁[t] := by rw [← e1, ← e2]; simp only [hagree]
        rw [this, hq] at h2; exact h2
    exact pairing_core E hE lam hT p hp r C₂ hC₂ hC₂r hlen L hLC₁ hagree hmax
      (by show lastHonestRound C₁ L + lam ≤ r; omega)

/-- At fixed `nBits`, `GetBlockProof` is the same for every header, so `nChainWork` is the length
of the chain times the proof of one block; this is why the paper (and `Chain.work`) measures
chains by their number of blocks. -/
theorem solution (S : BitcoinBlockV2.ChainState) (bits : ℕ)
    (h : ∀ hd ∈ S.headers, hd.bits = bits) :
    S.chainWork = S.headers.length * BitcoinBlockV2.blockProof bits := by
  unfold BitcoinBlockV2.ChainState.chainWork
  have : S.headers.map (fun hd => BitcoinBlockV2.blockProof hd.bits) =
      S.headers.map (fun _ => BitcoinBlockV2.blockProof bits) :=
    List.map_congr_left (fun hd hhd => by rw [h hd hhd])
  rw [this, List.map_const', List.sum_replicate, smul_eq_mul]
