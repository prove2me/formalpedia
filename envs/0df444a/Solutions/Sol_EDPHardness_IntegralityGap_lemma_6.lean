-- Prove2me | solution 1 for EDPHardness.IntegralityGap.lemma_6
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T10:35:26.627276+00:00
-- url     : https://prove2.me/submissions/84340f3f-abfe-416e-952f-bdc7b2d73fbe

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

namespace EDPLemma6Aux

open EDPHardness.IntegralityGap Real

/-- the number of `c`-subsets contained in a set `S` -/
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

/-- union bound: `Pr[ℰ₁] ≤ C(n,b) (1 - C(b,c)/C(n,c))^m` -/
lemma union_bound (n m c : ℕ) (hcn : c ≤ n) (hbn : badSize n c ≤ n) :
    hypProb n m c (E1 n c) ≤
      ((n.choose (badSize n c) : ℕ) : ℝ) *
        (1 - ((badSize n c).choose c : ℝ) / (n.choose c : ℝ)) ^ m := by
  classical
  set b := badSize n c
  set N := n.choose c
  have hNpos : 0 < N := Nat.choose_pos hcn
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hbc : b.choose c ≤ N := Nat.choose_le_choose c hbn
  have hcardHyp : Fintype.card (Hyp n m c) = N ^ m := by
    rw [Fintype.card_fun, Fintype.card_finset_len, Fintype.card_fin, Fintype.card_fin]
  -- the bad event is covered by a union
  set T : Finset (Fin n) → Finset (Hyp n m c) := fun S =>
    Fintype.piFinset (fun _ => Finset.univ.filter
      (fun s : {s : Finset (Fin n) // s.card = c} => ¬ s.1 ⊆ S))
  have hcover : (Finset.univ : Finset (Hyp n m c)).filter (E1 n c) ⊆
      (Finset.univ.powersetCard b).biUnion T := by
    intro H hH
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, E1] at hH
    obtain ⟨S, hS, hbad⟩ := hH
    rw [Finset.mem_biUnion]
    refine ⟨S, Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, hS⟩, ?_⟩
    simp only [T, Fintype.mem_piFinset, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hbad
  have hTcard : ∀ S ∈ Finset.univ.powersetCard b, (T S).card = (N - b.choose c) ^ m := by
    intro S hS
    rw [Finset.mem_powersetCard] at hS
    simp only [T, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    congr 1
    have h := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset {s : Finset (Fin n) // s.card = c}))
      (fun s : {s : Finset (Fin n) // s.card = c} => s.1 ⊆ S)
    rw [card_sub, hS.2, Finset.card_univ, Fintype.card_finset_len, Fintype.card_fin] at h
    omega
  have hcard : ((Finset.univ : Finset (Hyp n m c)).filter (E1 n c)).card ≤ n.choose b * (N - b.choose c) ^ m := by
    calc _ ≤ ((Finset.univ.powersetCard b).biUnion T).card := Finset.card_le_card hcover
      _ ≤ ∑ S ∈ Finset.univ.powersetCard b, (T S).card := Finset.card_biUnion_le
      _ = ∑ S ∈ Finset.univ.powersetCard b, (N - b.choose c) ^ m := Finset.sum_congr rfl hTcard
      _ = n.choose b * (N - b.choose c) ^ m := by
          rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
            smul_eq_mul]
  unfold hypProb
  rw [hcardHyp, div_le_iff₀ (by positivity)]
  have hR : (((Finset.univ : Finset (Hyp n m c)).filter (E1 n c)).card : ℝ) ≤
      (n.choose b : ℝ) * ((N : ℝ) - (b.choose c : ℝ)) ^ m := by
    have := (Nat.cast_le (α := ℝ)).2 hcard
    push_cast [Nat.cast_sub hbc] at this
    exact this
  have e : ((n.choose b : ℕ) : ℝ) * (1 - (b.choose c : ℝ) / (N : ℝ)) ^ m * ((N ^ m : ℕ) : ℝ)
      = (n.choose b : ℝ) * ((N : ℝ) - (b.choose c : ℝ)) ^ m := by
    push_cast
    rw [mul_assoc, ← mul_pow]
    congr 2
    field_simp
  rw [e]
  convert hR using 3

lemma fin_ineq (u l : ℝ) (hu : 16 ≤ u) (hl : 2.7 ≤ l) (hlu : 4 * l ≤ u) :
    (u + 1) * (1 + l) - (9 * u * l - 1) ≤ -3 := by nlinarith

lemma choose_exp_bound (n b : ℕ) (β : ℝ) (hβ : 0 < β) (hb : 1 ≤ b) (hnb : (n : ℝ) ≤ b * β) :
    (n.choose b : ℝ) ≤ Real.exp (b * (1 + Real.log β)) := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have h1 : (n.choose b : ℝ) ≤ (n : ℝ) ^ b / b.factorial := Nat.choose_le_pow_div b n
  have h2 : (b : ℝ) ^ b / b.factorial ≤ Real.exp b := Real.pow_div_factorial_le_exp (b : ℝ) hbR.le b
  have hf : (0 : ℝ) < b.factorial := by exact_mod_cast Nat.factorial_pos b
  have hbb : (0 : ℝ) < (b : ℝ) ^ b := by positivity
  have h3 : (n : ℝ) ^ b / b.factorial ≤ ((n : ℝ) / b) ^ b * Real.exp b := by
    rw [div_pow, div_le_iff₀ hf]
    rw [div_le_iff₀ hf] at h2
    have : (n : ℝ) ^ b = (n : ℝ) ^ b / (b : ℝ) ^ b * (b : ℝ) ^ b := by field_simp
    calc (n : ℝ) ^ b = (n : ℝ) ^ b / (b : ℝ) ^ b * (b : ℝ) ^ b := this
      _ ≤ (n : ℝ) ^ b / (b : ℝ) ^ b * (Real.exp b * b.factorial) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = _ := by ring
  have h4 : ((n : ℝ) / b) ^ b ≤ β ^ b := by
    apply pow_le_pow_left₀ (by positivity)
    rw [div_le_iff₀ hbR]; linarith
  have h5 : β ^ b = Real.exp (b * Real.log β) := by
    rw [Real.exp_nat_mul, Real.exp_log hβ]
  calc (n.choose b : ℝ) ≤ ((n : ℝ) / b) ^ b * Real.exp b := h1.trans h3
    _ ≤ β ^ b * Real.exp b := mul_le_mul_of_nonneg_right h4 (by positivity)
    _ = Real.exp (b * (1 + Real.log β)) := by
        rw [h5, ← Real.exp_add]; ring_nf

set_option maxHeartbeats 1000000 in
/-- the analytic part of Lemma 6 -/
lemma analytic (n c b m : ℕ) (β₁ : ℝ) (hc : 2 ≤ c) (hb1 : 16 ≤ β₁)
    (hbge : (n : ℝ) / β₁ ≤ b) (hble : (b : ℝ) ≤ n / β₁ + 1)
    (hm : 6 * (2 * β₁) ^ (c - 1) * Real.log β₁ * n - 1 ≤ m)
    (hcb : 4 * (c : ℝ) ^ 2 * β₁ ≤ n) (hbb : 4 * β₁ ^ 2 ≤ n) :
    (n.choose b : ℝ) * (1 - (b.choose c : ℝ) / (n.choose c : ℝ)) ^ m ≤ 1 / 4 := by
  have hβpos : 0 < β₁ := by linarith
  have hcR : (2 : ℝ) ≤ c := by exact_mod_cast hc
  have hnR : (0 : ℝ) < n := by
    have : 0 < 4 * β₁ ^ 2 := by positivity
    linarith
  set u := (n : ℝ) / β₁ with hu
  have hun : (n : ℝ) = u * β₁ := by rw [hu]; field_simp
  have hu_c : 4 * (c : ℝ) ^ 2 ≤ u := by
    rw [hu, le_div_iff₀ hβpos]; linarith
  have hu_b : 4 * β₁ ≤ u := by
    rw [hu, le_div_iff₀ hβpos]
    have : 4 * β₁ * β₁ = 4 * β₁ ^ 2 := by ring
    linarith
  have hc2 : (c : ℝ) ≤ (c : ℝ) ^ 2 := by
    have := mul_le_mul_of_nonneg_left (show (1:ℝ) ≤ c by linarith) (by linarith : (0:ℝ) ≤ c)
    have e : (c : ℝ) ^ 2 = c * c := by ring
    linarith
  have hu16 : 16 ≤ u := by linarith
  have hbR1 : (1 : ℝ) ≤ b := by linarith
  have hb1N : 1 ≤ b := by exact_mod_cast hbR1
  have hcb' : (c : ℝ) ≤ b := by linarith
  have hcbN : c ≤ b := by exact_mod_cast hcb'
  have hbn' : (b : ℝ) ≤ n := by
    have : u * 16 ≤ u * β₁ := mul_le_mul_of_nonneg_left hb1 (by linarith)
    linarith
  have hbnN : b ≤ n := by exact_mod_cast hbn'
  have hcnN : c ≤ n := le_trans hcbN hbnN
  -- logs
  set l := Real.log β₁ with hl
  have hl27 : 2.7 ≤ l := by
    have h16 : Real.log 16 ≤ l := Real.log_le_log (by norm_num) hb1
    have : Real.log 16 = 4 * Real.log 2 := by
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
    have := Real.log_two_gt_d9
    linarith
  have hlβ : l ≤ β₁ := by have := Real.log_le_sub_one_of_pos hβpos; linarith
  -- q
  set q := (b.choose c : ℝ) / (n.choose c : ℝ) with hq
  have hNc : (0 : ℝ) < n.choose c := by exact_mod_cast Nat.choose_pos hcnN
  have hq1 : q ≤ 1 := by
    rw [hq, div_le_one hNc]; exact_mod_cast Nat.choose_le_choose c hbnN
  have hq0 : 0 ≤ q := by positivity
  -- lower bound on q
  set w := 1 / β₁ ^ c with hw
  have hwpos : 0 < w := by positivity
  have hw1 : w ≤ 1 := by
    rw [hw, div_le_one (by positivity)]; exact one_le_pow₀ (by linarith)
  have hqlow : 3 / 4 * w ≤ q := by
    have hf : (0 : ℝ) < c.factorial := by exact_mod_cast Nat.factorial_pos c
    have hA : (((b + 1 - c : ℕ) : ℝ) ^ c) / c.factorial ≤ b.choose c := Nat.pow_le_choose c b
    have hB : (n.choose c : ℝ) ≤ (n : ℝ) ^ c / c.factorial := Nat.choose_le_pow_div c n
    have hcast : ((b + 1 - c : ℕ) : ℝ) = b + 1 - c := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [hcast] at hA
    have hy : 0 ≤ (b : ℝ) + 1 - c := by linarith
    have h1 : ((b : ℝ) + 1 - c) ^ c / (n : ℝ) ^ c ≤ q := by
      rw [hq]
      calc ((b : ℝ) + 1 - c) ^ c / (n : ℝ) ^ c
          = (((b : ℝ) + 1 - c) ^ c / c.factorial) / ((n : ℝ) ^ c / c.factorial) := by
            field_simp
        _ ≤ (b.choose c : ℝ) / (n.choose c : ℝ) :=
            div_le_div₀ (by positivity) hA hNc hB
    -- (b + 1 - c)/n ≥ (1/β₁)(1 - cβ₁/n)
    set a := -((c : ℝ) * β₁ / n) with ha
    have hcβ : (c : ℝ) * β₁ ≤ (c : ℝ) ^ 2 * β₁ := mul_le_mul_of_nonneg_right hc2 hβpos.le
    have ha2 : -2 ≤ a := by
      have : (c : ℝ) * β₁ / n ≤ 2 := by
        rw [div_le_iff₀ hnR]; linarith
      rw [ha]; linarith
    have hbern := one_add_mul_le_pow ha2 c
    have hca : 1 + (c : ℝ) * a ≥ 3 / 4 := by
      rw [ha]
      have : (c : ℝ) * ((c : ℝ) * β₁ / n) ≤ 1 / 4 := by
        rw [← mul_div_assoc, div_le_iff₀ hnR]
        have e : (c : ℝ) * ((c : ℝ) * β₁) = (c : ℝ) ^ 2 * β₁ := by ring
        rw [e]; linarith
      linarith
    have hlin : (1 / β₁) * (1 + a) ≤ ((b : ℝ) + 1 - c) / n := by
      rw [ha]
      have e : (1 / β₁) * (1 + -((c : ℝ) * β₁ / n)) = (u - c) / n := by
        rw [hu]; field_simp; ring
      rw [e]
      apply div_le_div_of_nonneg_right _ hnR.le
      linarith
    have ha0 : a ≤ 0 := by
      rw [ha]; have : 0 ≤ (c : ℝ) * β₁ / n := by positivity
      linarith
    have hca' : (c : ℝ) * a ≤ 1 * a := mul_le_mul_of_nonpos_right (by linarith) ha0
    have h1a : 0 ≤ 1 + a := by linarith
    have h2 : ((1 / β₁) * (1 + a)) ^ c ≤ (((b : ℝ) + 1 - c) / n) ^ c :=
      pow_le_pow_left₀ (by positivity) hlin c
    have h3 : (1 / β₁) ^ c = w := by rw [hw, div_pow, one_pow]
    rw [mul_pow, h3, div_pow] at h2
    have h4 : w * (3 / 4) ≤ w * (1 + a) ^ c :=
      mul_le_mul_of_nonneg_left (by linarith) hwpos.le
    linarith
  -- q m ≥ 9 u l - 1
  have hβw : 6 * (2 * β₁) ^ (c - 1) * l * n * w ≥ 12 * l * u := by
    have e : 6 * (2 * β₁) ^ (c - 1) * l * n * w = 6 * 2 ^ (c - 1) * l * u := by
      have : β₁ ^ c = β₁ ^ (c - 1) * β₁ := by
        rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ c)]
      rw [hw, hun, mul_pow, this]
      have hne : β₁ ^ (c - 1) * β₁ ≠ 0 := by positivity
      calc 6 * (2 ^ (c - 1) * β₁ ^ (c - 1)) * l * (u * β₁) * (1 / (β₁ ^ (c - 1) * β₁))
          = 6 * 2 ^ (c - 1) * l * u * ((β₁ ^ (c - 1) * β₁) * (1 / (β₁ ^ (c - 1) * β₁))) := by
            ring
        _ = 6 * 2 ^ (c - 1) * l * u := by rw [mul_one_div_cancel hne, mul_one]
    rw [e]
    have h2c : (2 : ℝ) ≤ 2 ^ (c - 1) := by
      have : (2 : ℝ) ^ 1 ≤ 2 ^ (c - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      simpa using this
    have hlu : 0 ≤ l * u := by positivity
    have := mul_le_mul_of_nonneg_right h2c hlu
    linarith
  have hqm : 9 * u * l - 3 / 4 ≤ m * q := by
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    have h1 : (m : ℝ) * (3 / 4 * w) ≤ m * q := mul_le_mul_of_nonneg_left hqlow hm0
    have h2 : (6 * (2 * β₁) ^ (c - 1) * l * n - 1) * (3 / 4 * w) ≤ m * (3 / 4 * w) :=
      mul_le_mul_of_nonneg_right hm (by positivity)
    linear_combination h1 + h2 + (3 / 4 : ℝ) * hβw + (3 / 4 : ℝ) * hw1
  -- final
  have hC := choose_exp_bound n b β₁ hβpos hb1N (by
    rw [hu, div_le_iff₀ hβpos] at hbge; linarith)
  have hpow : (1 - q) ^ m ≤ Real.exp (-(m * q)) := by
    calc (1 - q) ^ m ≤ (Real.exp (-q)) ^ m :=
          pow_le_pow_left₀ (by linarith) (Real.one_sub_le_exp_neg q) m
      _ = Real.exp (-(m * q)) := by rw [← Real.exp_nat_mul]; ring_nf
  have hexp : b * (1 + l) - m * q ≤ -3 := by
    have h1 : (b : ℝ) * (1 + l) ≤ (u + 1) * (1 + l) :=
      mul_le_mul_of_nonneg_right hble (by linarith)
    have := fin_ineq u l hu16 hl27 (by linarith)
    linarith
  calc (n.choose b : ℝ) * (1 - q) ^ m ≤ Real.exp (b * (1 + l)) * Real.exp (-(m * q)) :=
        mul_le_mul hC hpow (by positivity) (by positivity)
    _ = Real.exp (b * (1 + l) - m * q) := by rw [← Real.exp_add]; ring_nf
    _ ≤ Real.exp (-3) := Real.exp_le_exp.2 hexp
    _ ≤ 1 / 4 := by
        rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
        have := Real.add_one_le_exp 3
        linarith

end EDPLemma6Aux

open EDPHardness.IntegralityGap in
theorem solution :
    ∃ α : ℝ, 0 < α ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ c : ℕ, 2 ≤ c →
      (c : ℝ) ≤ α * Real.logb 2 (Real.logb 2 n) / Real.logb 2 (Real.logb 2 (Real.logb 2 n)) →
      hypProb n (numEdges n c) c (E1 n c) ≤ 1 / 4 := by
  obtain ⟨α, hα, N₀, hN⟩ := EDPLemma6Params.params6
  refine ⟨α, hα, N₀, ?_⟩
  intro n hn c hc hcα
  obtain ⟨hb1, hb1L, hcL, hL1, hL3⟩ := hN n hn c hc hcα
  set L := Real.logb 2 (n : ℝ)
  have hβpos : 0 < beta1 n c := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hcR : (0 : ℝ) ≤ c := Nat.cast_nonneg _
  -- c² β₁ ≤ L³, β₁² ≤ L³
  have hc2 : (c : ℝ) ^ 2 * beta1 n c ≤ L ^ 3 := by
    have h1 : (c : ℝ) ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ hcR hcL 2
    have := mul_le_mul h1 hb1L hβpos.le (by positivity)
    have e : L ^ 2 * L = L ^ 3 := by ring
    linarith
  have hbb2 : beta1 n c ^ 2 ≤ L ^ 3 := by
    have h1 : beta1 n c ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ hβpos.le hb1L 2
    have h2 : L ^ 2 * 1 ≤ L ^ 2 * L := mul_le_mul_of_nonneg_left hL1 (by positivity)
    have e : L ^ 2 * L = L ^ 3 := by ring
    linarith
  have hnR : (0 : ℝ) < n := by
    have : 0 < 4 * L ^ 3 := by positivity
    linarith
  -- b
  set b := badSize n c with hbdef
  have hbge : (n : ℝ) / beta1 n c ≤ b := Nat.le_ceil _
  have hble : (b : ℝ) ≤ n / beta1 n c + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hbn : b ≤ n := by
    have h1 : (n : ℝ) / beta1 n c ≤ n / 16 := div_le_div_of_nonneg_left hnR.le (by norm_num) hb1
    have h4 : (4 : ℝ) ≤ n := by
      have : (1 : ℝ) ≤ L ^ 3 := one_le_pow₀ hL1
      linarith
    have : (b : ℝ) ≤ n := by linarith
    exact_mod_cast this
  have hcn : c ≤ n := by
    have : (c : ℝ) ≤ n := by
      have : L ≤ L ^ 3 := by
        have h2 : L * 1 ≤ L * L ^ 2 := mul_le_mul_of_nonneg_left (one_le_pow₀ hL1) hL0
        have e : L * L ^ 2 = L ^ 3 := by ring
        linarith
      linarith
    exact_mod_cast this
  -- m
  have hm : 6 * (2 * beta1 n c) ^ (c - 1) * Real.log (beta1 n c) * n - 1 ≤ numEdges n c := by
    have h := Nat.lt_floor_add_one (beta2 n c * n)
    have e : (numEdges n c : ℝ) = ((⌊beta2 n c * n⌋₊ : ℕ) : ℝ) := rfl
    have e2 : beta2 n c = 6 * (2 * beta1 n c) ^ (c - 1) * Real.log (beta1 n c) := rfl
    rw [e, ← e2]
    linarith
  calc hypProb n (numEdges n c) c (E1 n c)
      ≤ ((n.choose b : ℕ) : ℝ) * (1 - (b.choose c : ℝ) / (n.choose c : ℝ)) ^ numEdges n c :=
        EDPLemma6Aux.union_bound n (numEdges n c) c hcn hbn
    _ ≤ 1 / 4 := EDPLemma6Aux.analytic n c b (numEdges n c) (beta1 n c) hc hb1 hbge hble hm
        (by linarith) (by linarith)
