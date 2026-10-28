-- Prove2me | solution 1 for DiscreteSearchGame.Optimal.lemma_9
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-24T11:41:21.346387+00:00
-- url     : https://prove2.me/submissions/95be3f2e-9c69-44fa-ad94-a4e6862ecec3

import Mathlib
import Definitions.Def_AllocationIndices_Jobs
import Definitions.Def_DiscreteSearchGame_Optimal_Model

set_option autoImplicit false

open AllocationIndices Filter Topology

open AllocationIndices in
lemma p2m4b_sc_eq {n : ℕ} (σ : ℕ → Fin n) (k : ℕ) (i : Fin n) :
    searchCount σ k i = ∑ t ∈ Finset.range k, if σ t = i then 1 else 0 := by
  unfold searchCount
  rw [Finset.card_filter]
  exact Fin.sum_univ_eq_sum_range (fun t => if σ t = i then 1 else 0) k

open AllocationIndices in
lemma p2m4b_sc_succ {n : ℕ} (σ : ℕ → Fin n) (k : ℕ) (i : Fin n) :
    searchCount σ (k + 1) i = searchCount σ k i + if σ k = i then 1 else 0 := by
  rw [p2m4b_sc_eq, p2m4b_sc_eq, Finset.sum_range_succ]

open AllocationIndices in
lemma p2m4b_sc_mono {n : ℕ} (σ : ℕ → Fin n) (i : Fin n) {k k' : ℕ} (h : k ≤ k') :
    searchCount σ k i ≤ searchCount σ k' i := by
  rw [p2m4b_sc_eq, p2m4b_sc_eq]
  exact Finset.sum_le_sum_of_subset (Finset.range_mono h)

open AllocationIndices in
lemma p2m4b_sum_sc {n : ℕ} (ξ : ℕ → Fin n) (m : ℕ) : ∑ i, searchCount ξ m i = m := by
  simp_rw [p2m4b_sc_eq]
  rw [Finset.sum_comm]
  simp

open AllocationIndices DiscreteSearchGame.Optimal in
lemma p2m4b_ruleCounts {n : ℕ} [NeZero n] (t q p : Fin n → ℝ) (r : Rule n) (k : ℕ)
    (i : Fin n) : ruleCounts t q p r k i = searchCount (ruleSeq t q r p) k i := by
  induction k generalizing i with
  | zero => simp [ruleCounts, searchCount]
  | succ k ih =>
    have h1 : ruleCounts t q p r (k + 1) i =
        ruleCounts t q p r k i + (Pi.single (ruleSeq t q r p k) 1 : Fin n → ℕ) i := rfl
    rw [h1, ih, p2m4b_sc_succ, Pi.single_apply]
    by_cases h : ruleSeq t q r p k = i
    · subst h; simp
    · rw [if_neg (Ne.symm h), if_neg h]

open DiscreteSearchGame.Optimal in
lemma p2m4b_tieBreak_max {n : ℕ} [NeZero n] (σ : Equiv.Perm (Fin n)) (f : Fin n → ℝ)
    (i : Fin n) : f i ≤ f (tieBreak σ f) := by
  unfold tieBreak
  set S := Finset.univ.filter fun j : Fin n => ∀ i, f i ≤ f (σ j) with hS
  have hm : ∀ H, S.min' H ∈ S := fun H => Finset.min'_mem S H
  exact (Finset.mem_filter.1 (hm _)).2 i

open DiscreteSearchGame.Optimal in
lemma p2m4b_tieBreak_min {n : ℕ} [NeZero n] (σ : Equiv.Perm (Fin n)) (f : Fin n → ℝ)
    (i j : Fin n) (hj : tieBreak σ f = j) (hle : f j ≤ f i) : σ.symm j ≤ σ.symm i := by
  have hmax : ∀ k, f k ≤ f j := fun k => hj ▸ p2m4b_tieBreak_max σ f k
  unfold tieBreak at hj
  set S := Finset.univ.filter fun l : Fin n => ∀ k, f k ≤ f (σ l) with hS
  have hmem : σ.symm i ∈ S := by
    rw [hS, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, fun k => ?_⟩
    rw [Equiv.apply_symm_apply]
    exact (hmax k).trans hle
  subst hj
  rw [Equiv.symm_apply_apply]
  exact Finset.min'_le S _ hmem

open AllocationIndices DiscreteSearchGame.Optimal in
lemma p2m4b_simple_index {n : ℕ} [NeZero n] (t q p : Fin n → ℝ)
    (σ : Equiv.Perm (Fin n)) (k : ℕ) (j : Fin n) : searchIndex p q t (simpleSeq t q σ p) k j =
      gittinsIndex t q p (ruleCounts t q p (fun _ => σ) k) j := by
  simp only [searchIndex, gittinsIndex, p2m4b_ruleCounts]
  rfl

open AllocationIndices DiscreteSearchGame.Optimal in
lemma p2m4b_simple_conforms {n : ℕ} [NeZero n] (t q p : Fin n → ℝ)
    (σ : Equiv.Perm (Fin n)) : ConformsToSearchIndex p q t (simpleSeq t q σ p) := by
  intro k i
  rw [p2m4b_simple_index, p2m4b_simple_index]
  exact p2m4b_tieBreak_max σ _ i

/-- The Gittins index of box `i` after `a` searches. -/
noncomputable def p2m4b_g {n : ℕ} (t q p : Fin n → ℝ) (i : Fin n) (a : ℕ) : ℝ :=
  p i * (1 - q i) ^ a * q i / t i

lemma p2m4b_g_anti {n : ℕ} (t q p : Fin n → ℝ) (ht : ∀ i, 0 < t i) (hq0 : ∀ i, 0 < q i)
    (hq1 : ∀ i, q i < 1) (hp : ∀ i, 0 < p i) (i : Fin n) : StrictAnti (p2m4b_g t q p i) := by
  intro a b hab
  unfold p2m4b_g
  have h1 : (1 - q i) ^ b < (1 - q i) ^ a :=
    pow_lt_pow_right_of_lt_one₀ (by linarith [hq1 i]) (by linarith [hq0 i]) hab
  have h2 : 0 < p i * q i := mul_pos (hp i) (hq0 i)
  apply div_lt_div_of_pos_right _ (ht i)
  nlinarith

lemma p2m4b_g_pos {n : ℕ} (t q p : Fin n → ℝ) (ht : ∀ i, 0 < t i) (hq0 : ∀ i, 0 < q i)
    (hq1 : ∀ i, q i < 1) (hp : ∀ i, 0 < p i) (i : Fin n) (a : ℕ) : 0 < p2m4b_g t q p i a := by
  unfold p2m4b_g
  have := hp i; have := hq0 i; have := ht i
  have : 0 < 1 - q i := by linarith [hq1 i]
  positivity

lemma p2m4b_g_small {n : ℕ} (t q p : Fin n → ℝ) (ht : ∀ i, 0 < t i) (hq0 : ∀ i, 0 < q i)
    (hq1 : ∀ i, q i < 1) (hp : ∀ i, 0 < p i) (i : Fin n) {ε : ℝ} (hε : 0 < ε) :
    ∃ A, ∀ a, A ≤ a → p2m4b_g t q p i a < ε := by
  have hc : 0 < p i * q i / t i := by have := hp i; have := hq0 i; have := ht i; positivity
  obtain ⟨A, hA⟩ := exists_pow_lt_of_lt_one (div_pos hε hc) (show 1 - q i < 1 by linarith [hq0 i])
  refine ⟨A, fun a ha => ?_⟩
  have h1 : (1 - q i) ^ a ≤ (1 - q i) ^ A :=
    pow_le_pow_of_le_one (by linarith [hq1 i]) (by linarith [hq0 i]) ha
  have h2 : p2m4b_g t q p i a = (p i * q i / t i) * (1 - q i) ^ a := by
    unfold p2m4b_g; ring
  rw [h2]
  calc (p i * q i / t i) * (1 - q i) ^ a ≤ (p i * q i / t i) * (1 - q i) ^ A := by gcongr
    _ < (p i * q i / t i) * (ε / (p i * q i / t i)) := by gcongr
    _ = ε := by rw [mul_comm]; exact div_mul_cancel₀ ε hc.ne'

open AllocationIndices in
lemma p2m4b_unbounded {n : ℕ} (t q p : Fin n → ℝ) (ht : ∀ i, 0 < t i) (hq0 : ∀ i, 0 < q i)
    (hq1 : ∀ i, q i < 1) (hp : ∀ i, 0 < p i) (ξ : ℕ → Fin n)
    (hξ : ConformsToSearchIndex p q t ξ) (j : Fin n) (B : ℕ) : ∃ m, B < searchCount ξ m j := by
  by_contra hcon
  push Not at hcon
  have hε := p2m4b_g_pos t q p ht hq0 hq1 hp j B
  have hA : ∀ i, ∃ A, ∀ a, A ≤ a → p2m4b_g t q p i a < p2m4b_g t q p j B :=
    fun i => p2m4b_g_small t q p ht hq0 hq1 hp i hε
  choose A hA using hA
  have hb : ∀ m i, searchCount ξ m i ≤ A i := by
    intro m
    induction m with
    | zero => intro i; simp [searchCount]
    | succ m ih =>
      intro i
      rw [p2m4b_sc_succ]
      split_ifs with h
      · have hk := hξ m j
        rw [h] at hk
        have hk' : p2m4b_g t q p j (searchCount ξ m j) ≤
            p2m4b_g t q p i (searchCount ξ m i) := hk
        have h1 : p2m4b_g t q p j B ≤ p2m4b_g t q p j (searchCount ξ m j) :=
          (p2m4b_g_anti t q p ht hq0 hq1 hp j).antitone (hcon m)
        have h2 : searchCount ξ m i < A i := by
          by_contra h3
          push Not at h3
          have := hA i _ h3
          linarith
        omega
      · simpa using ih i
  have h1 := p2m4b_sum_sc ξ (∑ i, A i + 1)
  have h2 : ∑ i, searchCount ξ (∑ i, A i + 1) i ≤ ∑ i, A i :=
    Finset.sum_le_sum fun i _ => hb _ i
  omega

open AllocationIndices in
lemma p2m4b_hit {n : ℕ} (t q p : Fin n → ℝ) (ht : ∀ i, 0 < t i) (hq0 : ∀ i, 0 < q i)
    (hq1 : ∀ i, q i < 1) (hp : ∀ i, 0 < p i) (ξ : ℕ → Fin n)
    (hξ : ConformsToSearchIndex p q t ξ) (j : Fin n) (b : ℕ) :
    ∃ m, ξ m = j ∧ searchCount ξ m j = b := by
  classical
  have hex := p2m4b_unbounded t q p ht hq0 hq1 hp ξ hξ j b
  obtain ⟨m0, hm0, hmin⟩ : ∃ m0, b < searchCount ξ m0 j ∧ ∀ m < m0, ¬ b < searchCount ξ m j :=
    ⟨Nat.find hex, Nat.find_spec hex, fun m hm => Nat.find_min hex hm⟩
  have hne : m0 ≠ 0 := by
    rintro rfl
    simp [searchCount] at hm0
  obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hne
  have hlt := hmin m' (Nat.lt_succ_self m')
  rw [p2m4b_sc_succ] at hm0
  by_cases h : ξ m' = j
  · refine ⟨m', h, ?_⟩
    rw [if_pos h] at hm0
    omega
  · rw [if_neg h] at hm0
    exact absurd hm0 hlt

open AllocationIndices in
lemma p2m4b_T {n : ℕ} (t q p : Fin n → ℝ) (ht : ∀ i, 0 < t i) (hq0 : ∀ i, 0 < q i)
    (hq1 : ∀ i, q i < 1) (hp : ∀ i, 0 < p i) (ξ : ℕ → Fin n)
    (hξ : ConformsToSearchIndex p q t ξ) :
    ∃ T : Fin n × ℕ → ℕ, (∀ x, ξ (T x) = x.1 ∧ searchCount ξ (T x) x.1 = x.2) ∧
      Function.Bijective T := by
  have hφinj : Function.Injective (fun k => (ξ k, searchCount ξ k (ξ k))) := by
    intro k k' hkk
    simp only [Prod.mk.injEq] at hkk
    obtain ⟨h1, h2⟩ := hkk
    by_contra hne
    have key : ∀ a b, a < b → ξ a = ξ b →
        searchCount ξ a (ξ a) < searchCount ξ b (ξ b) := by
      intro a b hab he
      have hm := p2m4b_sc_mono ξ (ξ a) (Nat.succ_le_of_lt hab)
      rw [p2m4b_sc_succ, if_pos rfl] at hm
      rw [← he]; omega
    rcases lt_or_gt_of_ne hne with hl | hl
    · have := key k k' hl h1; omega
    · have := key k' k hl h1.symm; omega
  choose T hT using fun x : Fin n × ℕ => p2m4b_hit t q p ht hq0 hq1 hp ξ hξ x.1 x.2
  refine ⟨T, hT, ?_, ?_⟩
  · intro x y hxy
    have hx := hT x
    have hy := hT y
    rw [hxy] at hx
    have e1 : x.1 = y.1 := hx.1.symm.trans hy.1
    refine Prod.ext e1 ?_
    rw [← hx.2, ← hy.2, e1]
  · intro m
    refine ⟨(ξ m, searchCount ξ m (ξ m)), hφinj ?_⟩
    obtain ⟨h1, h2⟩ := hT (ξ m, searchCount ξ m (ξ m))
    simp only at h1 h2 ⊢
    rw [h1, h2]

open AllocationIndices in
lemma p2m4b_order {n : ℕ} (t q p : Fin n → ℝ) (ht : ∀ i, 0 < t i) (hq0 : ∀ i, 0 < q i)
    (hq1 : ∀ i, q i < 1) (hp : ∀ i, 0 < p i) (ξ : ℕ → Fin n)
    (hξ : ConformsToSearchIndex p q t ξ) {i j : Fin n} {mi mj : ℕ} (hi : ξ mi = i)
    (hj : ξ mj = j) (hlt : mi < mj) :
    p2m4b_g t q p j (searchCount ξ mj j) ≤ p2m4b_g t q p i (searchCount ξ mi i) := by
  have hk := hξ mi j
  rw [hi] at hk
  have hk' : p2m4b_g t q p j (searchCount ξ mi j) ≤ p2m4b_g t q p i (searchCount ξ mi i) := hk
  have hmono : searchCount ξ mi j ≤ searchCount ξ mj j := p2m4b_sc_mono ξ j hlt.le
  exact ((p2m4b_g_anti t q p ht hq0 hq1 hp j).antitone hmono).trans hk'

open AllocationIndices in
lemma p2m4b_seg {n : ℕ} (ξ : ℕ → Fin n) {i : Fin n} {m' m : ℕ} (hi : ξ m' = i) :
    searchCount ξ m' i < searchCount ξ m i ↔ m' < m := by
  constructor
  · intro h
    by_contra h'
    push Not at h'
    have := p2m4b_sc_mono ξ i h'
    omega
  · intro h
    have h1 := p2m4b_sc_mono ξ i (Nat.succ_le_of_lt h)
    rw [p2m4b_sc_succ, if_pos hi] at h1
    omega

/-- Tie indicator: box `i`'s search at the tied level precedes box `j`'s `b`-th search. -/
noncomputable def p2m4b_tau {n : ℕ} (t q p : Fin n → ℝ) (T : Fin n × ℕ → ℕ) (i j : Fin n)
    (b : ℕ) : ℝ :=
  open Classical in
  if ∃ a, p2m4b_g t q p i a = p2m4b_g t q p j b ∧ T (i, a) < T (j, b) then 1 else 0

open AllocationIndices in
/-- The counts at box `j`'s `b`-th search, in terms of the index levels. -/
lemma p2m4b_cnt {n : ℕ} (t q p : Fin n → ℝ) (ht : ∀ i, 0 < t i) (hq0 : ∀ i, 0 < q i)
    (hq1 : ∀ i, q i < 1) (hp : ∀ i, 0 < p i) (ξ : ℕ → Fin n)
    (hξ : ConformsToSearchIndex p q t ξ) (T : Fin n × ℕ → ℕ)
    (hT : ∀ x, ξ (T x) = x.1 ∧ searchCount ξ (T x) x.1 = x.2) (i j : Fin n) (b : ℕ) (a : ℕ) :
    (p2m4b_g t q p j b < p2m4b_g t q p i a → a < searchCount ξ (T (j, b)) i) ∧
    (p2m4b_g t q p i a < p2m4b_g t q p j b → searchCount ξ (T (j, b)) i ≤ a) ∧
    (a < searchCount ξ (T (j, b)) i ↔ T (i, a) < T (j, b)) := by
  have hia := hT (i, a)
  have hjb := hT (j, b)
  simp only at hia hjb
  have hseg : a < searchCount ξ (T (j, b)) i ↔ T (i, a) < T (j, b) := by
    have := p2m4b_seg ξ (m := T (j, b)) hia.1
    rw [hia.2] at this
    exact this
  refine ⟨fun h => ?_, fun h => ?_, hseg⟩
  · rw [hseg]
    by_contra h'
    push Not at h'
    rcases h'.lt_or_eq with h'' | h''
    · have := p2m4b_order t q p ht hq0 hq1 hp ξ hξ hjb.1 hia.1 h''
      rw [hia.2, hjb.2] at this
      linarith
    · have e1 : j = i := by rw [← hjb.1, ← hia.1, h'']
      have e2 : b = a := by rw [← hjb.2, ← hia.2, h'', e1]
      subst e1 e2
      exact lt_irrefl _ h
  · by_contra h'
    push Not at h'
    have h2 := hseg.1 h'
    have := p2m4b_order t q p ht hq0 hq1 hp ξ hξ hia.1 hjb.1 h2
    rw [hia.2, hjb.2] at this
    linarith

open AllocationIndices in
/-- One term of `V_i`: tie case and no-tie case. -/
lemma p2m4b_term {n : ℕ} (t q p : Fin n → ℝ) (ht : ∀ i, 0 < t i) (hq0 : ∀ i, 0 < q i)
    (hq1 : ∀ i, q i < 1) (hp : ∀ i, 0 < p i) (ξ : ℕ → Fin n)
    (hξ : ConformsToSearchIndex p q t ξ) (T : Fin n × ℕ → ℕ)
    (hT : ∀ x, ξ (T x) = x.1 ∧ searchCount ξ (T x) x.1 = x.2) (i j : Fin n) (b : ℕ) :
    ((∀ a, p2m4b_g t q p i a ≠ p2m4b_g t q p j b) →
      (∀ a, a < searchCount ξ (T (j, b)) i ↔ p2m4b_g t q p j b < p2m4b_g t q p i a) ∧
      p2m4b_tau t q p T i j b = 0) ∧
    (∀ a, p2m4b_g t q p i a = p2m4b_g t q p j b →
      (1 - q i) ^ searchCount ξ (T (j, b)) i =
        (1 - q i) ^ a * (1 - q i * p2m4b_tau t q p T i j b)) := by
  have hanti := p2m4b_g_anti t q p ht hq0 hq1 hp i
  constructor
  · intro hne
    refine ⟨fun a => ⟨fun h => ?_, fun h => (p2m4b_cnt t q p ht hq0 hq1 hp ξ hξ T hT i j b a).1 h⟩, ?_⟩
    · rcases lt_trichotomy (p2m4b_g t q p j b) (p2m4b_g t q p i a) with h1 | h1 | h1
      · exact h1
      · exact absurd h1.symm (hne a)
      · have := (p2m4b_cnt t q p ht hq0 hq1 hp ξ hξ T hT i j b a).2.1 h1
        omega
    · unfold p2m4b_tau
      rw [if_neg]
      rintro ⟨a, ha, -⟩
      exact hne a ha
  · intro a ha
    have hc := p2m4b_cnt t q p ht hq0 hq1 hp ξ hξ T hT i j b
    have hup : searchCount ξ (T (j, b)) i ≤ a + 1 :=
      (hc (a + 1)).2.1 (by rw [← ha]; exact hanti (Nat.lt_succ_self a))
    have hlo : a ≤ searchCount ξ (T (j, b)) i := by
      rcases Nat.eq_zero_or_pos a with h0 | h0
      · omega
      · have := (hc (a - 1)).1 (by rw [← ha]; exact hanti (by omega))
        omega
    have htau : p2m4b_tau t q p T i j b = if T (i, a) < T (j, b) then 1 else 0 := by
      unfold p2m4b_tau
      congr 1
      apply propext
      constructor
      · rintro ⟨a', ha', hlt⟩
        have : a' = a := hanti.injective (ha'.trans ha.symm)
        subst this
        exact hlt
      · intro hlt
        exact ⟨a, ha, hlt⟩
    rw [htau]
    by_cases hlt : T (i, a) < T (j, b)
    · have : searchCount ξ (T (j, b)) i = a + 1 := by
        have := (hc a).2.2.2 hlt
        omega
      rw [this, if_pos hlt, pow_succ]
      ring
    · have : searchCount ξ (T (j, b)) i = a := by
        have : ¬ a < searchCount ξ (T (j, b)) i := fun h => hlt ((hc a).2.2.1 h)
        omega
      rw [this, if_neg hlt]
      ring


open AllocationIndices DiscreteSearchGame.Optimal in
/-- Every box is cheap to find under a Gittins sequence against `p` with `p i > 0`. -/
lemma p2m4b_V_lt_top {n : ℕ} (t q p : Fin n → ℝ) (ht : ∀ i, 0 < t i)
    (hq0 : ∀ i, 0 < q i) (hq1 : ∀ i, q i < 1) (hp0 : ∀ i, 0 ≤ p i) (ξ : ℕ → Fin n)
    (hξ : ConformsToSearchIndex p q t ξ) (i : Fin n) (hpi : 0 < p i) :
    V t q i ξ < ⊤ := by
  set c : ℝ := t i / (p i * q i) with hc
  have hc0 : 0 ≤ c := by have := ht i; have := hq0 i; positivity
  let h : Fin n × ℕ → ℝ := fun x => p x.1 * q x.1 * (1 - q x.1) ^ x.2
  have h0 : ∀ x, 0 ≤ h x := by
    intro x; have := hp0 x.1; have := hq0 x.1; have : 0 ≤ 1 - q x.1 := by linarith [hq1 x.1]
    positivity
  let φ : ℕ → Fin n × ℕ := fun k => (ξ k, searchCount ξ k (ξ k))
  have hpt : ∀ k, ENNReal.ofReal (t (ξ k) * (1 - q i) ^ searchCount ξ k i) ≤
      ENNReal.ofReal c * ENNReal.ofReal (h (φ k)) := by
    intro k
    rw [← ENNReal.ofReal_mul hc0]
    apply ENNReal.ofReal_le_ofReal
    have hk := hξ k i
    simp only [searchIndex] at hk
    rw [div_le_div_iff₀ (ht i) (ht (ξ k))] at hk
    simp only [h, φ, hc]
    rw [div_mul_eq_mul_div, le_div_iff₀ (by have := hpi; have := hq0 i; positivity)]
    nlinarith [hk]
  have hinj : Function.Injective φ := by
    intro k k' hkk
    simp only [φ, Prod.mk.injEq] at hkk
    obtain ⟨h1, h2⟩ := hkk
    by_contra hne
    have key : ∀ a b, a < b → ξ a = ξ b →
        searchCount ξ a (ξ a) < searchCount ξ b (ξ b) := by
      intro a b hab he
      have hm := p2m4b_sc_mono ξ (ξ a) (Nat.succ_le_of_lt hab)
      rw [p2m4b_sc_succ, if_pos rfl] at hm
      rw [← he]; omega
    rcases lt_or_gt_of_ne hne with hl | hl
    · have := key k k' hl h1; omega
    · have := key k' k hl h1.symm; omega
  have hsum : Summable h := by
    rw [summable_prod_of_nonneg h0]
    refine ⟨fun j => ?_, Summable.of_finite⟩
    show Summable fun m : ℕ => p j * q j * (1 - q j) ^ m
    exact (summable_geometric_of_lt_one (by linarith [hq1 j]) (by linarith [hq0 j])).mul_left _
  calc V t q i ξ = ∑' k, ENNReal.ofReal (t (ξ k) * (1 - q i) ^ searchCount ξ k i) := rfl
    _ ≤ ∑' k, ENNReal.ofReal c * ENNReal.ofReal (h (φ k)) := ENNReal.tsum_le_tsum hpt
    _ = ENNReal.ofReal c * ∑' k, ENNReal.ofReal (h (φ k)) := ENNReal.tsum_mul_left
    _ ≤ ENNReal.ofReal c * ∑' x, ENNReal.ofReal (h x) := by
        gcongr
        exact ENNReal.tsum_comp_le_tsum_of_injective hinj _
    _ = ENNReal.ofReal c * ENNReal.ofReal (∑' x, h x) := by
        rw [ENNReal.ofReal_tsum_of_nonneg h0 hsum]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

lemma p2m4b_tau_tie {n : ℕ} (t q p : Fin n → ℝ) (T : Fin n × ℕ → ℕ) (i j : Fin n) (a b : ℕ)
    (hinj : Function.Injective (p2m4b_g t q p i))
    (ha : p2m4b_g t q p i a = p2m4b_g t q p j b) :
    p2m4b_tau t q p T i j b = if T (i, a) < T (j, b) then 1 else 0 := by
  unfold p2m4b_tau
  congr 1
  apply propext
  constructor
  · rintro ⟨a', ha', hlt⟩
    have : a' = a := hinj (ha'.trans ha.symm)
    subst this
    exact hlt
  · intro hlt
    exact ⟨a, ha, hlt⟩

lemma p2m4b_tau_none {n : ℕ} (t q p : Fin n → ℝ) (T : Fin n × ℕ → ℕ) (i j : Fin n) (b : ℕ)
    (hno : ∀ a, p2m4b_g t q p i a ≠ p2m4b_g t q p j b) : p2m4b_tau t q p T i j b = 0 := by
  unfold p2m4b_tau
  rw [if_neg]
  rintro ⟨a, ha, -⟩
  exact hno a ha

lemma p2m4b_tau_self {n : ℕ} (t q p : Fin n → ℝ) (T : Fin n × ℕ → ℕ) (i : Fin n) (b : ℕ)
    (hinj : Function.Injective (p2m4b_g t q p i)) : p2m4b_tau t q p T i i b = 0 := by
  unfold p2m4b_tau
  rw [if_neg]
  rintro ⟨a, ha, hlt⟩
  have : a = b := hinj ha
  subst this
  exact lt_irrefl _ hlt

open AllocationIndices in
lemma p2m4b_tau_swap {n : ℕ} (t q p : Fin n → ℝ) (ht : ∀ i, 0 < t i) (hq0 : ∀ i, 0 < q i)
    (hq1 : ∀ i, q i < 1) (hp : ∀ i, 0 < p i) (ξ : ℕ → Fin n) (T : Fin n × ℕ → ℕ)
    (hT : ∀ x, ξ (T x) = x.1 ∧ searchCount ξ (T x) x.1 = x.2) {i j : Fin n} (hij : i ≠ j)
    {a b : ℕ} (ha : p2m4b_g t q p i a = p2m4b_g t q p j b) :
    p2m4b_tau t q p T j i a = 1 - p2m4b_tau t q p T i j b := by
  rw [p2m4b_tau_tie t q p T i j a b (p2m4b_g_anti t q p ht hq0 hq1 hp i).injective ha,
    p2m4b_tau_tie t q p T j i b a (p2m4b_g_anti t q p ht hq0 hq1 hp j).injective ha.symm]
  have e1 := (hT (i, a)).1
  have e2 := (hT (j, b)).1
  simp only at e1 e2
  have hne : T (i, a) ≠ T (j, b) := fun h => hij (e1.symm.trans ((congrArg ξ h).trans e2))
  rcases lt_or_gt_of_ne hne with h | h
  · rw [if_pos h, if_neg (not_lt.2 h.le)]; norm_num
  · rw [if_neg (not_lt.2 h.le), if_pos h]; norm_num

open AllocationIndices in
lemma p2m4b_diff {n : ℕ} (t q p : Fin n → ℝ) (ht : ∀ i, 0 < t i) (hq0 : ∀ i, 0 < q i)
    (hq1 : ∀ i, q i < 1) (hp : ∀ i, 0 < p i) (ξ ξ' : ℕ → Fin n)
    (hξ : ConformsToSearchIndex p q t ξ) (hξ' : ConformsToSearchIndex p q t ξ')
    (T T' : Fin n × ℕ → ℕ)
    (hT : ∀ x, ξ (T x) = x.1 ∧ searchCount ξ (T x) x.1 = x.2)
    (hT' : ∀ x, ξ' (T' x) = x.1 ∧ searchCount ξ' (T' x) x.1 = x.2) (i j : Fin n) (b : ℕ) :
    (1 - q i) ^ searchCount ξ (T (j, b)) i - (1 - q i) ^ searchCount ξ' (T' (j, b)) i =
      t i / p i * (p2m4b_g t q p j b *
        (p2m4b_tau t q p T' i j b - p2m4b_tau t q p T i j b)) := by
  by_cases htie : ∃ a, p2m4b_g t q p i a = p2m4b_g t q p j b
  · obtain ⟨a, ha⟩ := htie
    rw [(p2m4b_term t q p ht hq0 hq1 hp ξ hξ T hT i j b).2 a ha,
      (p2m4b_term t q p ht hq0 hq1 hp ξ' hξ' T' hT' i j b).2 a ha, ← ha]
    unfold p2m4b_g
    have ht' := (ht i).ne'
    have hp' := (hp i).ne'
    field_simp
    ring
  · push Not at htie
    obtain ⟨h1, h2⟩ := (p2m4b_term t q p ht hq0 hq1 hp ξ hξ T hT i j b).1 htie
    obtain ⟨h1', h2'⟩ := (p2m4b_term t q p ht hq0 hq1 hp ξ' hξ' T' hT' i j b).1 htie
    have : searchCount ξ (T (j, b)) i = searchCount ξ' (T' (j, b)) i := by
      apply le_antisymm
      · by_contra h
        push Not at h
        exact lt_irrefl _ ((h1' _).2 ((h1 _).1 h))
      · by_contra h
        push Not at h
        exact lt_irrefl _ ((h1 _).2 ((h1' _).1 h))
    rw [this, h2, h2']
    ring

open AllocationIndices in
lemma p2m4b_pair {n : ℕ} (t q p : Fin n → ℝ) (ht : ∀ i, 0 < t i) (hq0 : ∀ i, 0 < q i)
    (hq1 : ∀ i, q i < 1) (hp : ∀ i, 0 < p i) (ξ ξ' : ℕ → Fin n)
    (T T' : Fin n × ℕ → ℕ)
    (hT : ∀ x, ξ (T x) = x.1 ∧ searchCount ξ (T x) x.1 = x.2)
    (hT' : ∀ x, ξ' (T' x) = x.1 ∧ searchCount ξ' (T' x) x.1 = x.2) (i j : Fin n)
    (hij : i ≠ j) :
    ∑' a, p2m4b_g t q p i a * (p2m4b_tau t q p T' j i a - p2m4b_tau t q p T j i a) =
      - ∑' b, p2m4b_g t q p j b * (p2m4b_tau t q p T' i j b - p2m4b_tau t q p T i j b) := by
  have hai := (p2m4b_g_anti t q p ht hq0 hq1 hp i).injective
  have haj := (p2m4b_g_anti t q p ht hq0 hq1 hp j).injective
  set f : ℕ → ℝ := fun b =>
    -(p2m4b_g t q p j b * (p2m4b_tau t q p T' i j b - p2m4b_tau t q p T i j b)) with hf
  set g : ℕ → ℝ := fun a =>
    p2m4b_g t q p i a * (p2m4b_tau t q p T' j i a - p2m4b_tau t q p T j i a) with hg
  have hswap : ∀ a b, p2m4b_g t q p i a = p2m4b_g t q p j b → g a = f b := by
    intro a b hab
    simp only [hf, hg]
    rw [p2m4b_tau_swap t q p ht hq0 hq1 hp ξ T hT hij hab,
      p2m4b_tau_swap t q p ht hq0 hq1 hp ξ' T' hT' hij hab, hab]
    ring
  have hsupp_g : ∀ a, g a ≠ 0 → ∃ b, p2m4b_g t q p j b = p2m4b_g t q p i a := by
    intro a ha
    by_contra hno
    push Not at hno
    apply ha
    simp only [hg]
    rw [p2m4b_tau_none t q p T j i a hno, p2m4b_tau_none t q p T' j i a hno]
    ring
  have hsupp_f : ∀ b, f b ≠ 0 → ∃ a, p2m4b_g t q p i a = p2m4b_g t q p j b := by
    intro b hb
    by_contra hno
    push Not at hno
    apply hb
    simp only [hf]
    rw [p2m4b_tau_none t q p T i j b hno, p2m4b_tau_none t q p T' i j b hno]
    ring
  have hfg : ∑' b, f b = ∑' a, g a := by
    refine tsum_eq_tsum_of_ne_zero_bij (fun a => Classical.choose (hsupp_g a.1 a.2)) ?_ ?_ ?_
    · intro x y hxy
      have hx := Classical.choose_spec (hsupp_g x.1 x.2)
      have hy := Classical.choose_spec (hsupp_g y.1 y.2)
      simp only at hxy
      rw [hxy] at hx
      exact Subtype.ext (hai (hx.symm.trans hy))
    · intro b hb
      obtain ⟨a, ha⟩ := hsupp_f b hb
      have hga : g a ≠ 0 := by rw [hswap a b ha]; exact hb
      refine ⟨⟨a, hga⟩, ?_⟩
      have hs := Classical.choose_spec (hsupp_g a hga)
      exact haj (hs.trans ha)
    · intro x
      exact (hswap x.1 _ (Classical.choose_spec (hsupp_g x.1 x.2)).symm).symm
  rw [← tsum_neg]
  exact hfg.symm

open AllocationIndices DiscreteSearchGame.Optimal in
lemma p2m4b_V_repr {n : ℕ} (t q : Fin n → ℝ) (ht : ∀ i, 0 < t i) (hq1 : ∀ i, q i < 1)
    (ξ : ℕ → Fin n) (T : Fin n × ℕ → ℕ)
    (hT : ∀ x, ξ (T x) = x.1 ∧ searchCount ξ (T x) x.1 = x.2)
    (hTb : Function.Bijective T) (i : Fin n) (hfin : V t q i ξ ≠ ⊤) :
    HasSum (fun x : Fin n × ℕ => t x.1 * (1 - q i) ^ searchCount ξ (T x) i)
      (V t q i ξ).toReal := by
  have h0 : ∀ m, 0 ≤ t (ξ m) * (1 - q i) ^ searchCount ξ m i := by
    intro m
    have h1 := ht (ξ m)
    have h2 : 0 ≤ 1 - q i := by linarith [hq1 i]
    positivity
  let e := Equiv.ofBijective T hTb
  have hV : V t q i ξ =
      ∑' x, ENNReal.ofReal (t (ξ (T x)) * (1 - q i) ^ searchCount ξ (T x) i) :=
    (e.tsum_eq (fun m => ENNReal.ofReal (t (ξ m) * (1 - q i) ^ searchCount ξ m i))).symm
  rw [hV] at hfin ⊢
  have hs := ENNReal.summable_toReal hfin
  rw [ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
  have hfun : (fun x : Fin n × ℕ =>
      (ENNReal.ofReal (t (ξ (T x)) * (1 - q i) ^ searchCount ξ (T x) i)).toReal) =
      fun x => t x.1 * (1 - q i) ^ searchCount ξ (T x) i := by
    funext x
    rw [ENNReal.toReal_ofReal (h0 _), (hT x).1]
  rw [hfun] at hs ⊢
  exact hs.hasSum

open AllocationIndices DiscreteSearchGame.Optimal in
lemma p2m4b_cV_diff {n : ℕ} (t q p : Fin n → ℝ) (ht : ∀ i, 0 < t i) (hq0 : ∀ i, 0 < q i)
    (hq1 : ∀ i, q i < 1) (hp : ∀ i, 0 < p i) (ξ ξ' : ℕ → Fin n)
    (hξ : ConformsToSearchIndex p q t ξ) (hξ' : ConformsToSearchIndex p q t ξ')
    (T T' : Fin n × ℕ → ℕ)
    (hT : ∀ x, ξ (T x) = x.1 ∧ searchCount ξ (T x) x.1 = x.2)
    (hT' : ∀ x, ξ' (T' x) = x.1 ∧ searchCount ξ' (T' x) x.1 = x.2)
    (hTb : Function.Bijective T) (hTb' : Function.Bijective T') (c : Fin n → ℝ) :
    ∑ i, c i * vecReal t q ξ i - ∑ i, c i * vecReal t q ξ' i =
      ∑ i, ∑ j, c i / p i * t i * t j * ∑' b, p2m4b_g t q p j b *
        (p2m4b_tau t q p T' i j b - p2m4b_tau t q p T i j b) := by
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hfin : V t q i ξ ≠ ⊤ :=
    (p2m4b_V_lt_top t q p ht hq0 hq1 (fun k => (hp k).le) ξ hξ i (hp i)).ne
  have hfin' : V t q i ξ' ≠ ⊤ :=
    (p2m4b_V_lt_top t q p ht hq0 hq1 (fun k => (hp k).le) ξ' hξ' i (hp i)).ne
  have h3 := (p2m4b_V_repr t q ht hq1 ξ T hT hTb i hfin).sub
    (p2m4b_V_repr t q ht hq1 ξ' T' hT' hTb' i hfin')
  have hfun : (fun x : Fin n × ℕ => t x.1 * (1 - q i) ^ searchCount ξ (T x) i -
      t x.1 * (1 - q i) ^ searchCount ξ' (T' x) i) = fun x => t x.1 * (t i / p i *
        (p2m4b_g t q p x.1 x.2 * (p2m4b_tau t q p T' i x.1 x.2 - p2m4b_tau t q p T i x.1 x.2))) := by
    funext x
    obtain ⟨j, b⟩ := x
    dsimp only
    rw [← mul_sub, p2m4b_diff t q p ht hq0 hq1 hp ξ ξ' hξ hξ' T T' hT hT' i j b]
  rw [hfun] at h3
  unfold vecReal
  rw [← mul_sub, ← h3.tsum_eq, h3.summable.tsum_prod, tsum_fintype, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  dsimp only
  rw [tsum_mul_left, tsum_mul_left]
  ring

open AllocationIndices DiscreteSearchGame.Optimal in
lemma p2m4b_pref {n : ℕ} [NeZero n] (t q p : Fin n → ℝ) (ht : ∀ i, 0 < t i)
    (hq0 : ∀ i, 0 < q i) (hq1 : ∀ i, q i < 1) (hp : ∀ i, 0 < p i)
    (σ : Equiv.Perm (Fin n)) (T : Fin n × ℕ → ℕ)
    (hT : ∀ x, simpleSeq t q σ p (T x) = x.1 ∧ searchCount (simpleSeq t q σ p) (T x) x.1 = x.2)
    {i j : Fin n} {a b : ℕ} (hσ : σ.symm i < σ.symm j)
    (hab : p2m4b_g t q p i a = p2m4b_g t q p j b) : T (i, a) < T (j, b) := by
  have hia := hT (i, a)
  have hjb := hT (j, b)
  simp only at hia hjb
  have hij : i ≠ j := fun h => by rw [h] at hσ; exact lt_irrefl _ hσ
  have hne : T (i, a) ≠ T (j, b) :=
    fun h => hij (hia.1.symm.trans ((congrArg _ h).trans hjb.1))
  rcases lt_or_gt_of_ne hne with h | h
  · exact h
  · exfalso
    have hNi : searchCount (simpleSeq t q σ p) (T (j, b)) i ≤ a := by
      by_contra h'
      push Not at h'
      have := (p2m4b_seg (simpleSeq t q σ p) (m := T (j, b)) hia.1).1 (by rw [hia.2]; exact h')
      omega
    have hle : p2m4b_g t q p j b ≤ p2m4b_g t q p i (searchCount (simpleSeq t q σ p) (T (j, b)) i) := by
      rw [← hab]
      exact (p2m4b_g_anti t q p ht hq0 hq1 hp i).antitone hNi
    have hm : tieBreak σ (gittinsIndex t q p (ruleCounts t q p (fun _ => σ) (T (j, b)))) = j :=
      hjb.1
    have h2 := p2m4b_tieBreak_min σ _ i j hm (by
      rw [← p2m4b_simple_index t q p σ (T (j, b)) j, ← p2m4b_simple_index t q p σ (T (j, b)) i]
      show p2m4b_g t q p j (searchCount (simpleSeq t q σ p) (T (j, b)) j) ≤
        p2m4b_g t q p i (searchCount (simpleSeq t q σ p) (T (j, b)) i)
      rw [hjb.2]
      exact hle)
    exact absurd hσ (not_lt.2 h2)

open AllocationIndices DiscreteSearchGame.Optimal in
lemma p2m4b_key {n : ℕ} [NeZero n] (t q p : Fin n → ℝ) (ht : ∀ i, 0 < t i)
    (hq0 : ∀ i, 0 < q i) (hq1 : ∀ i, q i < 1) (hp : ∀ i, 0 < p i) (ξ : ℕ → Fin n)
    (hξ : ConformsToSearchIndex p q t ξ) (c : Fin n → ℝ) :
    ∃ σ : Equiv.Perm (Fin n),
      ∑ i, c i * vecReal t q (simpleSeq t q σ p) i ≤ ∑ i, c i * vecReal t q ξ i := by
  set r : Fin n → ℝ := fun i => c i / p i with hr
  set σ := Tuple.sort (fun i => - r i) with hσ
  have hmono := Tuple.monotone_sort (fun i => - r i)
  have hσr : ∀ i j, σ.symm i < σ.symm j → r j ≤ r i := by
    intro i j h
    have := hmono h.le
    simp only [Function.comp, ← hσ, Equiv.apply_symm_apply] at this
    linarith
  refine ⟨σ, ?_⟩
  obtain ⟨T, hT, hTb⟩ := p2m4b_T t q p ht hq0 hq1 hp ξ hξ
  obtain ⟨T', hT', hTb'⟩ :=
    p2m4b_T t q p ht hq0 hq1 hp (simpleSeq t q σ p) (p2m4b_simple_conforms t q p σ)
  have hd := p2m4b_cV_diff t q p ht hq0 hq1 hp ξ (simpleSeq t q σ p) hξ
    (p2m4b_simple_conforms t q p σ) T T' hT hT' hTb hTb' c
  set Δ : Fin n → Fin n → ℝ := fun i j => ∑' b, p2m4b_g t q p j b *
    (p2m4b_tau t q p T' i j b - p2m4b_tau t q p T i j b) with hΔ
  have hd' : ∑ i, c i * vecReal t q ξ i - ∑ i, c i * vecReal t q (simpleSeq t q σ p) i =
      ∑ i, ∑ j, r i * t i * t j * Δ i j := hd
  have hanti : ∀ i j, Δ j i = - Δ i j := by
    intro i j
    by_cases hij : i = j
    · subst hij
      have : Δ i i = 0 := by
        simp only [hΔ]
        have hinj := (p2m4b_g_anti t q p ht hq0 hq1 hp i).injective
        simp [p2m4b_tau_self t q p T i _ hinj, p2m4b_tau_self t q p T' i _ hinj]
      linarith
    · exact p2m4b_pair t q p ht hq0 hq1 hp ξ (simpleSeq t q σ p) T T' hT hT' i j hij
  have hpos : ∀ i j, σ.symm i < σ.symm j → 0 ≤ Δ i j := by
    intro i j h
    apply tsum_nonneg
    intro b
    apply mul_nonneg (p2m4b_g_pos t q p ht hq0 hq1 hp j b).le
    have : p2m4b_tau t q p T i j b ≤ p2m4b_tau t q p T' i j b := by
      by_cases h1 : ∃ a, p2m4b_g t q p i a = p2m4b_g t q p j b ∧ T (i, a) < T (j, b)
      · obtain ⟨a, ha, -⟩ := h1
        have h2 : ∃ a, p2m4b_g t q p i a = p2m4b_g t q p j b ∧ T' (i, a) < T' (j, b) :=
          ⟨a, ha, p2m4b_pref t q p ht hq0 hq1 hp σ T' hT' h ha⟩
        unfold p2m4b_tau
        rw [if_pos h2]
        split_ifs <;> norm_num
      · unfold p2m4b_tau
        rw [if_neg h1]
        split_ifs <;> norm_num
    linarith
  have key : 0 ≤ ∑ i, ∑ j, r i * t i * t j * Δ i j := by
    have h2 : ∑ i, ∑ j, r i * t i * t j * Δ i j = ∑ i, ∑ j, -(r j * t i * t j * Δ i j) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [hanti]
      ring
    have h3 : 0 ≤ ∑ i, ∑ j, (r i - r j) * t i * t j * Δ i j := by
      apply Finset.sum_nonneg
      intro i _
      apply Finset.sum_nonneg
      intro j _
      have hti := (ht i).le
      have htj := (ht j).le
      rcases lt_trichotomy (σ.symm i) (σ.symm j) with h | h | h
      · have h1 := hσr i j h
        have h2 := hpos i j h
        exact mul_nonneg (mul_nonneg (mul_nonneg (by linarith) hti) htj) h2
      · have : i = j := σ.symm.injective h
        subst this
        simp
      · have h1 := hσr j i h
        have h2 := hpos j i h
        rw [hanti j i]
        have := mul_nonneg (mul_nonneg (mul_nonneg (sub_nonneg.2 h1) hti) htj) h2
        linarith
    have h4 : ∑ i, ∑ j, (r i - r j) * t i * t j * Δ i j =
        ∑ i, ∑ j, r i * t i * t j * Δ i j + ∑ i, ∑ j, -(r j * t i * t j * Δ i j) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    linarith
  linarith

open AllocationIndices Filter Topology DiscreteSearchGame.Optimal in
theorem solution {n : ℕ} [NeZero n] (t q : Fin n → ℝ) (ht : ∀ i, 0 < t i) (hq0 : ∀ i, 0 < q i)
    (hq1 : ∀ i, q i < 1)
    (p : Fin n → ℝ) (hp : p ∈ stdSimplex ℝ (Fin n)) (hpos : ∀ i, 0 < p i) :
    convexHull ℝ (payoffSet t q p) = convexHull ℝ (simplePayoffSet t q p) := by
  apply le_antisymm
  · apply convexHull_min _ (convex_convexHull ℝ _)
    rintro v ⟨ξ, hξ, rfl⟩
    have hfin : (simplePayoffSet t q p).Finite := (Set.finite_range _).image _
    have hK := (hfin.isCompact_convexHull ℝ).isClosed
    by_contra hv
    obtain ⟨f, u, hfu, hu⟩ := geometric_hahn_banach_point_closed (convex_convexHull ℝ _) hK hv
    set c : Fin n → ℝ := fun i => f (fun j => if i = j then 1 else 0) with hc
    have hf : ∀ y : Fin n → ℝ, f y = ∑ i, c i * y i := by
      intro y
      conv_lhs => rw [pi_eq_sum_univ y]
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, smul_eq_mul, mul_comm]
    obtain ⟨σ, hσ⟩ := p2m4b_key t q p ht hq0 hq1 hpos ξ hξ c
    have hmem : vecReal t q (simpleSeq t q σ p) ∈ convexHull ℝ (simplePayoffSet t q p) :=
      subset_convexHull ℝ _ ⟨_, ⟨σ, rfl⟩, rfl⟩
    have h1 := hu _ hmem
    rw [hf] at h1
    rw [hf] at hfu
    linarith
  · apply convexHull_mono
    rintro v ⟨ξ, ⟨σ, rfl⟩, rfl⟩
    exact ⟨_, p2m4b_simple_conforms t q p σ, rfl⟩
