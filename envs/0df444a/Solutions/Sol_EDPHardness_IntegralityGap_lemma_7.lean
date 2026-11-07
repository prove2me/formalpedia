-- Prove2me | solution 1 for EDPHardness.IntegralityGap.lemma_7
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T10:43:21.129303+00:00
-- url     : https://prove2.me/submissions/d6e55951-8f41-4ff2-9f52-86dae10ecf19

import Mathlib
import Definitions.Def_EDPHardness_IntegralityGap_GapInstance

namespace EDPLemma6Params

open EDPHardness.IntegralityGap Real

lemma logb_le_quarter (x : ℝ) (hx : 0 ≤ x) : logb 2 x ≤ 6 * x ^ ((1 : ℝ) / 4) := by
  have h1 := Real.log_le_rpow_div hx (ε := 1 / 4) (by norm_num)
  have h2 := Real.log_two_gt_d9
  have hp : 0 ≤ x ^ ((1 : ℝ) / 4) := Real.rpow_nonneg hx _
  unfold logb
  rw [div_le_iff₀ (by linarith)]
  have : x ^ ((1 : ℝ) / 4) / (1 / 4) = 4 * x ^ ((1 : ℝ) / 4) := by ring
  rw [this] at h1
  nlinarith

lemma quarter_pow (x : ℝ) (hx : 0 ≤ x) : (x ^ ((1 : ℝ) / 4)) ^ 4 = x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]; norm_num

lemma quarter_ge (x : ℝ) (hx : 256 ≤ x) : 4 ≤ x ^ ((1 : ℝ) / 4) := by
  have h := quarter_pow x (by linarith)
  have hp : 0 ≤ x ^ ((1 : ℝ) / 4) := Real.rpow_nonneg (by linarith) _
  by_contra hlt
  push_neg at hlt
  have : (x ^ ((1 : ℝ) / 4)) ^ 4 < 4 ^ 4 := by
    apply pow_lt_pow_left₀ hlt hp (by norm_num)
  rw [h] at this
  norm_num at this
  linarith

lemma two_mul_le_two_pow (c : ℕ) : 2 * c ≤ 2 ^ c := by
  induction c with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; simp
    · omega

lemma aux64 (s : ℝ) (h : 4 ≤ s) : 64 * s ≤ s ^ 4 := by nlinarith [sq_nonneg s, sq_nonneg (s - 4)]

set_option maxHeartbeats 1000000 in
theorem params6 :
    ∃ α : ℝ, 0 < α ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ c : ℕ, 2 ≤ c →
      (c : ℝ) ≤ α * Real.logb 2 (Real.logb 2 n) / Real.logb 2 (Real.logb 2 (Real.logb 2 n)) →
      16 ≤ beta1 n c ∧ beta1 n c ≤ Real.logb 2 n ∧ (c : ℝ) ≤ Real.logb 2 n ∧
      1 ≤ Real.logb 2 n ∧ 4 * (Real.logb 2 n) ^ 3 ≤ (n : ℝ) := by
  refine ⟨1 / 12, by norm_num, ⌈(2 : ℝ) ^ ((2 : ℝ) ^ (256 : ℝ))⌉₊, ?_⟩
  intro n hn c hc hcα
  -- basic logarithms
  set L1 := logb 2 (n : ℝ) with hL1
  set L2 := logb 2 L1 with hL2
  set L3 := logb 2 L2 with hL3
  have hnR : (2 : ℝ) ^ ((2 : ℝ) ^ (256 : ℝ)) ≤ n := Nat.ceil_le.1 hn
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le (by positivity) hnR
  have hL1big : (2 : ℝ) ^ (256 : ℝ) ≤ L1 := by
    have : logb 2 ((2 : ℝ) ^ ((2 : ℝ) ^ (256 : ℝ))) ≤ L1 :=
      (Real.logb_le_logb (by norm_num) (by positivity) hnpos).2 hnR
    rwa [Real.logb_rpow (by norm_num) (by norm_num)] at this
  have hL1pos : 0 < L1 := lt_of_lt_of_le (by positivity) hL1big
  have hL2big : 256 ≤ L2 := by
    have : logb 2 ((2 : ℝ) ^ (256 : ℝ)) ≤ L2 :=
      (Real.logb_le_logb (by norm_num) (by positivity) hL1pos).2 hL1big
    rwa [Real.logb_rpow (by norm_num) (by norm_num)] at this
  have hL1_256 : 256 ≤ L1 := by
    refine le_trans ?_ hL1big
    have : (2 : ℝ) ^ (8 : ℝ) ≤ (2 : ℝ) ^ (256 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    refine le_trans (le_of_eq ?_) this
    rw [show (8 : ℝ) = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
  have hL2pos : 0 < L2 := by linarith
  have hL3one : 1 ≤ L3 := by
    rw [hL3, Real.le_logb_iff_rpow_le (by norm_num) hL2pos]; norm_num; linarith
  have hL1eq : (2 : ℝ) ^ L2 = L1 := Real.rpow_logb (by norm_num) (by norm_num) hL1pos
  have hneq : (2 : ℝ) ^ L1 = n := Real.rpow_logb (by norm_num) (by norm_num) hnpos
  have hlogL1 : Real.log L1 = L2 * Real.log 2 := by
    rw [hL2, Real.logb, div_mul_cancel₀ _ (Real.log_pos (by norm_num : (1:ℝ) < 2)).ne']
  have hL3le := logb_le_quarter L2 hL2pos.le
  have hL2le := logb_le_quarter L1 hL1pos.le
  set t := L2 ^ ((1 : ℝ) / 4) with ht
  set s := L1 ^ ((1 : ℝ) / 4) with hs
  have ht4 : t ^ 4 = L2 := quarter_pow L2 hL2pos.le
  have hs4 : s ^ 4 = L1 := quarter_pow L1 hL1pos.le
  have ht_ge : 4 ≤ t := quarter_ge L2 hL2big
  have hs_ge : 4 ≤ s := quarter_ge L1 hL1_256
  -- c ≤ L2 / 6
  have hcR : (2 : ℝ) ≤ c := by exact_mod_cast hc
  have hcpos : (0 : ℝ) < c := by linarith
  have hcL2 : (c : ℝ) ≤ L2 / 12 := by
    refine hcα.trans ?_
    rw [div_le_iff₀ (by linarith)]
    have := mul_le_mul_of_nonneg_left hL3one (by positivity : (0:ℝ) ≤ L2 / 12)
    linarith
  -- X
  set X := L1 / (150 * L2 ^ 2) with hX
  have hXpos : 0 < X := by positivity
  have hlog150 : logb 2 (150 : ℝ) ≤ 8 := by
    have : logb 2 (150 : ℝ) ≤ logb 2 ((2 : ℝ) ^ (8 : ℕ)) :=
      (Real.logb_le_logb (by norm_num) (by norm_num) (by norm_num)).2 (by norm_num)
    rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num)] at this
    simpa using this
  have hlogX : logb 2 X = L2 - logb 2 150 - 2 * L3 := by
    rw [hX, Real.logb_div hL1pos.ne' (by positivity), Real.logb_mul (by norm_num) (by positivity),
      Real.logb_pow]
    push_cast; ring
  have hlogX_ge : L2 / 2 ≤ logb 2 X := by
    rw [hlogX]
    have ht3 : (4 : ℝ) ^ 3 ≤ t ^ 3 := pow_le_pow_left₀ (by norm_num) ht_ge 3
    have ht4' : t ^ 4 = t ^ 3 * t := by ring
    have h64 : 64 * t ≤ t ^ 3 * t := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    linarith
  -- β₁
  have hb1def : beta1 n c = (1 / 4) * X ^ ((1 : ℝ) / c) := rfl
  set Z := X ^ ((1 : ℝ) / c) with hZ
  have hZpos : 0 < Z := Real.rpow_pos_of_pos hXpos _
  have hZ8 : 64 ≤ Z := by
    have h3 : (6 : ℝ) ≤ logb 2 Z := by
      rw [hZ, Real.logb_rpow_eq_mul_logb_of_pos hXpos]
      rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hcpos]
      linarith
    rw [Real.le_logb_iff_rpow_le (by norm_num) hZpos] at h3
    norm_num at h3
    exact h3
  have hXge1 : 1 ≤ X := by
    by_contra h
    push_neg at h
    have : Z ≤ 1 := Real.rpow_le_one hXpos.le h.le (by positivity)
    linarith
  have hb1 : 16 ≤ beta1 n c := by rw [hb1def]; linarith
  have hXL1 : X ≤ L1 := by
    rw [hX, div_le_iff₀ (by positivity)]
    have h1 : (1 : ℝ) ≤ 150 * L2 ^ 2 := by
      have : (256 : ℝ) * 256 ≤ L2 * L2 := mul_le_mul hL2big hL2big (by norm_num) (by linarith)
      nlinarith
    exact le_mul_of_one_le_right hL1pos.le h1
  have hZX : Z ≤ X := by
    have : X ^ ((1 : ℝ) / c) ≤ X ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hXge1 (by rw [div_le_one hcpos]; linarith)
    rw [Real.rpow_one] at this; exact this
  have h64 := aux64 s hs_ge
  refine ⟨hb1, by rw [hb1def]; linarith, by linarith, by linarith, ?_⟩
  -- 4 L1^3 ≤ n
  rw [← hneq]
  have e1 : 4 * L1 ^ 3 = (2 : ℝ) ^ (2 + L2 * ((3 : ℕ) : ℝ)) := by
    rw [Real.rpow_add (by norm_num), ← hL1eq, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  rw [e1]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  push_cast
  linarith

end EDPLemma6Params

namespace EDPLemma7Aux

open EDPHardness.IntegralityGap Real

lemma card_sub (n c : ℕ) (S : Finset (Fin n)) :
    (Finset.univ.filter (fun s : {s : Finset (Fin n) // s.card = c} => s.1 ⊆ S)).card =
      S.card.choose c := by
  rw [← Finset.card_powersetCard]
  rw [← Finset.card_map (Function.Embedding.subtype _)]
  congr 1
  ext s
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
    Function.Embedding.coe_subtype, Finset.mem_powersetCard]
  constructor
  · rintro ⟨x, hx, rfl⟩; exact ⟨hx, x.2⟩
  · rintro ⟨h1, h2⟩; exact ⟨⟨s, h2⟩, h1, rfl⟩

/-- `c`-subsets containing a fixed vertex: `n * #A = c * C(n,c)` -/
lemma card_containing (n c : ℕ) (hc : 1 ≤ c) (v : Fin n) :
    n * (Finset.univ.filter (fun s : {s : Finset (Fin n) // s.card = c} => v ∈ s.1)).card =
      c * n.choose c := by
  classical
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by have := v.2; omega⟩
  obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
  have h := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset {s : Finset (Fin (n' + 1)) // s.card = c' + 1}))
    (fun s => v ∈ s.1)
  rw [Finset.card_univ, Fintype.card_finset_len, Fintype.card_fin] at h
  have e : (Finset.univ.filter
      (fun s : {s : Finset (Fin (n' + 1)) // s.card = c' + 1} => ¬ v ∈ s.1)) =
      Finset.univ.filter (fun s : {s : Finset (Fin (n' + 1)) // s.card = c' + 1} =>
        s.1 ⊆ Finset.univ.erase v) := by
    ext s; simp [Finset.subset_erase]
  rw [e, card_sub, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    Fintype.card_fin, Nat.add_sub_cancel, Nat.choose_succ_succ'] at h
  have hA : (Finset.univ.filter
      (fun s : {s : Finset (Fin (n' + 1)) // s.card = c' + 1} => v ∈ s.1)).card =
      n'.choose c' := by omega
  rw [hA, Nat.add_one_mul_choose_eq, mul_comm]

lemma Hyp_card (n m c : ℕ) : Fintype.card (Hyp n m c) = (n.choose c) ^ m := by
  rw [Fintype.card_fun, Fintype.card_finset_len, Fintype.card_fin, Fintype.card_fin]

/-- `#{H : deg_H(v) ≥ k} ≤ C(m,k) A^k N^(m-k)` -/
lemma deg_count (n m c k : ℕ) (hkm : k ≤ m) (v : Fin n) :
    (Finset.univ.filter (fun H : Hyp n m c => k ≤ degH H v)).card ≤
      m.choose k *
        ((Finset.univ.filter (fun s : {s : Finset (Fin n) // s.card = c} => v ∈ s.1)).card ^ k *
          (n.choose c) ^ (m - k)) := by
  classical
  set A := Finset.univ.filter (fun s : {s : Finset (Fin n) // s.card = c} => v ∈ s.1)
  set T : Finset (Fin m) → Finset (Hyp n m c) := fun K =>
    Fintype.piFinset (fun i => if i ∈ K then A else Finset.univ)
  have hcover : (Finset.univ.filter (fun H : Hyp n m c => k ≤ degH H v)) ⊆
      (Finset.univ.powersetCard k).biUnion T := by
    intro H hH
    rw [Finset.mem_filter] at hH
    have hH := hH.2
    unfold degH at hH
    obtain ⟨K, hKsub, hKcard⟩ := Finset.exists_subset_card_eq hH
    rw [Finset.mem_biUnion]
    refine ⟨K, Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, hKcard⟩, ?_⟩
    simp only [T, Fintype.mem_piFinset]
    intro i
    split_ifs with hi
    · have := hKsub hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
      simp [A, this]
    · exact Finset.mem_univ _
  have hT : ∀ K ∈ Finset.univ.powersetCard k, (T K).card = A.card ^ k * (n.choose c) ^ (m - k) := by
    intro K hK
    rw [Finset.mem_powersetCard] at hK
    simp only [T, Fintype.card_piFinset, apply_ite Finset.card]
    rw [Finset.prod_ite]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_finset_len, Fintype.card_fin]
    congr 2
    · rw [Finset.filter_mem_eq_inter, Finset.univ_inter, hK.2]
    · have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin m)))
        (fun i => i ∈ K)
      rw [Finset.filter_mem_eq_inter, Finset.univ_inter, hK.2, Finset.card_univ,
        Fintype.card_fin] at this
      omega
  calc _ ≤ ((Finset.univ.powersetCard k).biUnion T).card := Finset.card_le_card hcover
    _ ≤ ∑ K ∈ Finset.univ.powersetCard k, (T K).card := Finset.card_biUnion_le
    _ = ∑ K ∈ Finset.univ.powersetCard k, A.card ^ k * (n.choose c) ^ (m - k) :=
        Finset.sum_congr rfl hT
    _ = _ := by
        rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
          smul_eq_mul]

/-- Markov + double counting: `Pr[ℰ₂] ≤ β₁ · C(m,k) (c/n)^k` -/
lemma markov_bound (n m c k : ℕ) (hc : 1 ≤ c) (hcn : c ≤ n) (hkm : k ≤ m) (β : ℝ)
    (hβ : 0 < β) (hk : ∀ H : Hyp n m c, ∀ v, 10 * beta2 n c * c < (degH H v : ℝ) → k ≤ degH H v)
    (hβ1 : beta1 n c = β) :
    hypProb n m c (E2 n c) ≤ β * (m.choose k : ℝ) * ((c : ℝ) / n) ^ k := by
  classical
  have hn : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  set N := n.choose c
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.choose_pos hcn
  -- high-degree set
  set hi : Hyp n m c → Finset (Fin n) := fun H =>
    Finset.univ.filter (fun v => 10 * beta2 n c * c < (degH H v : ℝ))
  set E := (Finset.univ : Finset (Hyp n m c)).filter (E2 n c)
  -- Σ_H #hi(H) ≤ n C(m,k) A^k N^(m-k)
  have hsum : ∑ H : Hyp n m c, ((hi H).card : ℝ) ≤
      ∑ v : Fin n, ((Finset.univ.filter (fun H : Hyp n m c => k ≤ degH H v)).card : ℝ) := by
    have e : ∑ H : Hyp n m c, ((hi H).card : ℝ) =
        ∑ v : Fin n, ((Finset.univ.filter
          (fun H : Hyp n m c => 10 * beta2 n c * c < (degH H v : ℝ))).card : ℝ) := by
      simp only [hi, Finset.card_filter, Nat.cast_sum]
      rw [Finset.sum_comm]
    rw [e]
    apply Finset.sum_le_sum
    intro v _
    exact_mod_cast Finset.card_le_card (fun H hH => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hH ⊢
      exact hk H v hH)
  have hE : (E.card : ℝ) * (n / β) ≤ ∑ H : Hyp n m c, ((hi H).card : ℝ) := by
    calc (E.card : ℝ) * (n / β) = ∑ _H ∈ E, ((n : ℝ) / β) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ H ∈ E, ((hi H).card : ℝ) := by
          apply Finset.sum_le_sum
          intro H hH
          simp only [E, Finset.mem_filter, Finset.mem_univ, true_and, E2] at hH
          rw [hβ1] at hH
          exact hH.le
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun _ _ _ => Nat.cast_nonneg _)
  -- per-vertex count
  have hv : ∀ v : Fin n,
      ((Finset.univ.filter (fun H : Hyp n m c => k ≤ degH H v)).card : ℝ) ≤
        (m.choose k : ℝ) * ((c : ℝ) / n) ^ k * (N : ℝ) ^ m := by
    intro v
    have h1 := deg_count n m c k hkm v
    have h2 := card_containing n c hc v
    set a := (Finset.univ.filter (fun s : {s : Finset (Fin n) // s.card = c} => v ∈ s.1)).card
    have ha : (a : ℝ) = (c : ℝ) / n * N := by
      have : (n : ℝ) * a = c * N := by exact_mod_cast h2
      field_simp; linarith
    have h1R : ((Finset.univ.filter (fun H : Hyp n m c => k ≤ degH H v)).card : ℝ) ≤
        (m.choose k : ℝ) * ((a : ℝ) ^ k * (N : ℝ) ^ (m - k)) := by exact_mod_cast h1
    rw [ha, mul_pow] at h1R
    have e : (N : ℝ) ^ m = (N : ℝ) ^ k * (N : ℝ) ^ (m - k) := by
      rw [← pow_add, Nat.add_sub_cancel' hkm]
    rw [e]
    calc _ ≤ _ := h1R
      _ = _ := by ring
  have htot : (E.card : ℝ) * (n / β) ≤ n * ((m.choose k : ℝ) * ((c : ℝ) / n) ^ k * (N : ℝ) ^ m) := by
    calc _ ≤ _ := hE
      _ ≤ _ := hsum
      _ ≤ ∑ _v : Fin n, (m.choose k : ℝ) * ((c : ℝ) / n) ^ k * (N : ℝ) ^ m :=
          Finset.sum_le_sum (fun v _ => hv v)
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  unfold hypProb
  rw [Hyp_card, div_le_iff₀ (by exact_mod_cast pow_pos (Nat.choose_pos hcn) m)]
  have hNm : (0 : ℝ) < (N : ℝ) ^ m := by positivity
  have key : (E.card : ℝ) ≤ β * ((m.choose k : ℝ) * ((c : ℝ) / n) ^ k * (N : ℝ) ^ m) := by
    have h := htot
    rw [div_eq_mul_inv, ← mul_assoc] at h
    have h' : (E.card : ℝ) * n ≤ n * ((m.choose k : ℝ) * ((c : ℝ) / n) ^ k * (N : ℝ) ^ m) * β := by
      have := mul_le_mul_of_nonneg_right h hβ.le
      rwa [mul_assoc (E.card * (n : ℝ)), inv_mul_cancel₀ hβ.ne', mul_one] at this
    have h'' : (E.card : ℝ) * n ≤ (β * ((m.choose k : ℝ) * ((c : ℝ) / n) ^ k * (N : ℝ) ^ m)) * n := by
      linarith
    exact le_of_mul_le_mul_right h'' hnR
  push_cast
  refine le_trans (le_of_eq ?_) (key.trans (le_of_eq ?_))
  · simp only [E]
  · simp only [N]; ring

end EDPLemma7Aux

namespace EDPLemma7Fin

open EDPHardness.IntegralityGap

lemma choose_bound (m k : ℕ) (x : ℝ) (hx : 0 ≤ x) (hk : 1 ≤ k) (hm : (m : ℝ) * x ≤ k / 2 / Real.exp 1) :
    (m.choose k : ℝ) * x ^ k ≤ (1 / 2) ^ k := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have h1 : (m.choose k : ℝ) ≤ (m : ℝ) ^ k / k.factorial := Nat.choose_le_pow_div k m
  have h2 : (k : ℝ) ^ k / k.factorial ≤ Real.exp k := Real.pow_div_factorial_le_exp (k : ℝ) hkR.le k
  have hf : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have hmx0 : 0 ≤ (m : ℝ) * x := by positivity
  calc (m.choose k : ℝ) * x ^ k ≤ (m : ℝ) ^ k / k.factorial * x ^ k :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = ((m : ℝ) * x) ^ k / k.factorial := by rw [mul_pow]; ring
    _ ≤ (k / 2 / Real.exp 1) ^ k / k.factorial := by
        apply div_le_div_of_nonneg_right _ hf.le
        exact pow_le_pow_left₀ hmx0 hm k
    _ = (1 / 2) ^ k * ((k : ℝ) ^ k / k.factorial) / Real.exp k := by
        rw [show Real.exp k = Real.exp 1 ^ k by rw [← Real.exp_nat_mul]; ring_nf]
        field_simp
        rw [← mul_pow, ← mul_pow]
        congr 1
        field_simp
    _ ≤ (1 / 2) ^ k * Real.exp k / Real.exp k := by
        apply div_le_div_of_nonneg_right _ (Real.exp_pos _).le
        exact mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = (1 / 2) ^ k := by field_simp

end EDPLemma7Fin

open EDPHardness.IntegralityGap in
theorem solution :
    ∃ α : ℝ, 0 < α ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ c : ℕ, 2 ≤ c →
      (c : ℝ) ≤ α * Real.logb 2 (Real.logb 2 n) / Real.logb 2 (Real.logb 2 (Real.logb 2 n)) →
      hypProb n (numEdges n c) c (E2 n c) ≤ 1 / 4 := by
  obtain ⟨α, hα, N₀, hN⟩ := EDPLemma6Params.params6
  refine ⟨α, hα, N₀, ?_⟩
  intro n hn c hc hcα
  obtain ⟨hb1, hb1L, hcL, hL1, hL3⟩ := hN n hn c hc hcα
  set L := Real.logb 2 (n : ℝ)
  set β := beta1 n c with hβdef
  have hβpos : 0 < β := by linarith
  have hcR : (2 : ℝ) ≤ c := by exact_mod_cast hc
  have hL3' : L ≤ L ^ 3 := by
    have h2 : L * 1 ≤ L * L ^ 2 := mul_le_mul_of_nonneg_left (one_le_pow₀ hL1) (by linarith)
    have e : L * L ^ 2 = L ^ 3 := by ring
    linarith
  have hnR : (0 : ℝ) < n := by
    have : 0 < 4 * L ^ 3 := by positivity
    linarith
  have hcn' : 12 * (c : ℝ) ≤ n := by
    have hc0 : (0 : ℝ) ≤ c := by linarith
    have h1 : (c : ℝ) ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ hc0 hcL 2
    have h2 := mul_le_mul h1 hb1L hβpos.le (by positivity)
    have e : L ^ 2 * L = L ^ 3 := by ring
    have h3 : (2 : ℝ) * 16 ≤ c * β := mul_le_mul hcR hb1 (by norm_num) hc0
    have h4 : (c : ℝ) * (2 * 16) ≤ c * (c * β) := mul_le_mul_of_nonneg_left h3 hc0
    have e2 : (c : ℝ) * (c * β) = c ^ 2 * β := by ring
    linarith
  have hcn : c ≤ n := by
    have : (c : ℝ) ≤ n := by linarith
    exact_mod_cast this
  -- β₂ ≥ β₁
  set β₂ := beta2 n c with hβ₂def
  have hβ₂e : β₂ = 6 * (2 * β) ^ (c - 1) * Real.log β := rfl
  have hl : 2.7 ≤ Real.log β := by
    have h16 : Real.log 16 ≤ Real.log β := Real.log_le_log (by norm_num) hb1
    have : Real.log 16 = 4 * Real.log 2 := by
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
    have := Real.log_two_gt_d9
    linarith
  have hpow : 2 * β ≤ (2 * β) ^ (c - 1) := by
    have := pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ 2 * β) (by omega : 1 ≤ c - 1)
    simpa using this
  have hβ₂ : β ≤ β₂ := by
    rw [hβ₂e]
    have h1 : 2 * β * 2.7 ≤ (2 * β) ^ (c - 1) * Real.log β :=
      mul_le_mul hpow hl (by norm_num) (by positivity)
    linarith
  have hβ₂pos : 0 < β₂ := by linarith
  -- k
  set x := 10 * β₂ * c with hx
  have hx0 : 0 ≤ x := by positivity
  set k := ⌊x⌋₊ + 1 with hk
  have hkx : x < k := by rw [hk]; push_cast; exact Nat.lt_floor_add_one x
  have hkx' : (k : ℝ) ≤ x + 1 := by rw [hk]; push_cast; linarith [Nat.floor_le hx0]
  have hk1 : 1 ≤ k := by omega
  have hdeg : ∀ H : Hyp n (numEdges n c) c, ∀ v,
      10 * beta2 n c * c < (degH H v : ℝ) → k ≤ degH H v := by
    intro H v h
    have : ⌊x⌋₊ < degH H v := (Nat.floor_lt hx0).2 h
    omega
  -- m
  set m := numEdges n c with hmdef
  have hm_le : (m : ℝ) ≤ β₂ * n := Nat.floor_le (by positivity)
  have hm_ge : β₂ * n - 1 ≤ m := by
    have h := Nat.lt_floor_add_one (β₂ * n)
    have e : (m : ℝ) = ((⌊β₂ * n⌋₊ : ℕ) : ℝ) := rfl
    rw [e]; linarith
  have hkm : k ≤ m := by
    have h1 : β₂ * (12 * c) ≤ β₂ * n := mul_le_mul_of_nonneg_left hcn' hβ₂pos.le
    have h2 : (2 : ℝ) ≤ β₂ * (2 * c) := by nlinarith
    have : (k : ℝ) ≤ m := by nlinarith
    exact_mod_cast this
  have hM := EDPLemma7Aux.markov_bound n m c k (by omega) hcn hkm β hβpos hdeg rfl
  -- analytic
  have hxk : (m : ℝ) * ((c : ℝ) / n) ≤ k / 2 / Real.exp 1 := by
    have he := Real.exp_one_lt_d9
    have he0 := Real.exp_pos 1
    have h1 : (m : ℝ) * ((c : ℝ) / n) ≤ β₂ * c := by
      rw [mul_div_assoc', div_le_iff₀ hnR]
      have := mul_le_mul_of_nonneg_right hm_le (by positivity : (0 : ℝ) ≤ c)
      linarith
    rw [div_div, le_div_iff₀ (by positivity)]
    have h2 : (m : ℝ) * ((c : ℝ) / n) * (2 * Real.exp 1) ≤ β₂ * c * (2 * 2.72) :=
      mul_le_mul h1 (by linarith) (by positivity) (by positivity)
    linarith
  have hC := EDPLemma7Fin.choose_bound m k ((c : ℝ) / n) (by positivity) hk1 hxk
  have h2k : 4 * β ≤ (2 : ℝ) ^ k := by
    have h1 : (k : ℝ) < (2 : ℝ) ^ k := by exact_mod_cast Nat.lt_two_pow_self
    have h2 : 20 * β ≤ x := by
      rw [hx]
      have := mul_le_mul hβ₂ hcR (by norm_num) hβ₂pos.le
      linarith
    linarith
  calc hypProb n m c (E2 n c) ≤ β * (m.choose k : ℝ) * ((c : ℝ) / n) ^ k := hM
    _ = β * ((m.choose k : ℝ) * ((c : ℝ) / n) ^ k) := by ring
    _ ≤ β * (1 / 2) ^ k := mul_le_mul_of_nonneg_left hC hβpos.le
    _ ≤ 1 / 4 := by
        rw [div_pow, one_pow, mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
        linarith
