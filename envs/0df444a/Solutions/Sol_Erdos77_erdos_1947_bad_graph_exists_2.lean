-- Prove2me | solution 2 for Erdos77.erdos_1947_bad_graph_exists
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T05:56:46.887784+00:00
-- url     : https://prove2.me/submissions/bfe55165-b234-4783-9184-aa9cb5cfccb1

import Mathlib

set_option autoImplicit false

namespace Erdos77Aux6c7f

open Finset

lemma fact_sq (k : ℕ) (hk : 3 ≤ k) : 4 * 2 ^ k < (k.factorial) ^ 2 := by
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    rw [Nat.factorial_succ, mul_pow, pow_succ]
    have h4 : 4 ≤ (k + 1) ^ 2 := by nlinarith
    have hp : 0 < (k.factorial) ^ 2 := by positivity
    nlinarith

lemma card_const {α : Type} [Fintype α] [DecidableEq α] (A : Finset α) (b : Bool) :
    (univ.filter (fun c : α → Bool => ∀ e ∈ A, c e = b)).card * 2 ^ A.card
      = 2 ^ Fintype.card α := by
  have h : univ.filter (fun c : α → Bool => ∀ e ∈ A, c e = b) =
      Fintype.piFinset (fun e => if e ∈ A then ({b} : Finset Bool) else univ) := by
    ext c
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro h e
      split_ifs with he
      · simp [h e he]
      · simp
    · intro h e he
      have := h e
      simpa [he] using this
  rw [h, Fintype.card_piFinset]
  have hi : ∀ i, (if i ∈ A then ({b} : Finset Bool) else univ).card = if i ∈ A then 1 else 2 := by
    intro i; split_ifs <;> simp
  simp_rw [hi]
  rw [Finset.prod_ite]
  simp only [Finset.prod_const_one, one_mul, Finset.prod_const]
  rw [← pow_add]
  congr 1
  have h1 : (univ.filter (fun x => x ∈ A)) = A := by ext; simp
  have h2 := Finset.card_filter_add_card_filter_not (s := (univ : Finset α)) (fun x => x ∈ A)
  rw [h1, card_univ] at h2
  omega

theorem bad_coloring (n k : ℕ) (h : 2 * n.choose k < 2 ^ k.choose 2) :
    ∃ c : Finset (Fin n) → Bool, ∀ s : Finset (Fin n), s.card = k → ∀ b : Bool,
      ∃ e ∈ s.powersetCard 2, c e ≠ b := by
  classical
  by_contra hne
  push Not at hne
  set F : Finset (Fin n) → Bool → Finset (Finset (Fin n) → Bool) := fun s b =>
    univ.filter (fun c : Finset (Fin n) → Bool => ∀ e ∈ s.powersetCard 2, c e = b) with hF
  have hsub : (univ : Finset (Finset (Fin n) → Bool)) ⊆
      ((univ : Finset (Fin n)).powersetCard k).biUnion
        (fun s => (univ : Finset Bool).biUnion (fun b => F s b)) := by
    intro c _
    obtain ⟨s, hs, b, hb⟩ := hne c
    simp only [mem_biUnion, mem_univ, true_and]
    refine ⟨s, by simp [mem_powersetCard, hs], b, ?_⟩
    simp only [hF, mem_filter, mem_univ, true_and]
    exact hb
  have h1 := (card_le_card hsub).trans card_biUnion_le
  have h2 : ∀ s ∈ (univ : Finset (Fin n)).powersetCard k,
      ((univ : Finset Bool).biUnion (fun b => F s b)).card * 2 ^ k.choose 2
        ≤ 2 * 2 ^ Fintype.card (Finset (Fin n)) := by
    intro s hs
    rw [mem_powersetCard] at hs
    have hm : (s.powersetCard 2).card = k.choose 2 := by
      rw [card_powersetCard, hs.2]
    calc ((univ : Finset Bool).biUnion (fun b => F s b)).card * 2 ^ k.choose 2
        ≤ (∑ b : Bool, (F s b).card) * 2 ^ k.choose 2 :=
          Nat.mul_le_mul_right _ card_biUnion_le
      _ = ∑ b : Bool, (F s b).card * 2 ^ k.choose 2 := by rw [Finset.sum_mul]
      _ = ∑ _b : Bool, 2 ^ Fintype.card (Finset (Fin n)) := by
          apply Finset.sum_congr rfl
          intro b _
          rw [← hm]
          exact card_const _ b
      _ = 2 * 2 ^ Fintype.card (Finset (Fin n)) := by simp
  have h3 : (univ : Finset (Finset (Fin n) → Bool)).card * 2 ^ k.choose 2 ≤
      ((univ : Finset (Fin n)).powersetCard k).card *
        (2 * 2 ^ Fintype.card (Finset (Fin n))) := by
    calc (univ : Finset (Finset (Fin n) → Bool)).card * 2 ^ k.choose 2
        ≤ (∑ s ∈ (univ : Finset (Fin n)).powersetCard k,
            ((univ : Finset Bool).biUnion (fun b => F s b)).card) * 2 ^ k.choose 2 :=
          Nat.mul_le_mul_right _ h1
      _ = ∑ s ∈ (univ : Finset (Fin n)).powersetCard k,
            ((univ : Finset Bool).biUnion (fun b => F s b)).card * 2 ^ k.choose 2 := by
          rw [Finset.sum_mul]
      _ ≤ ∑ _s ∈ (univ : Finset (Fin n)).powersetCard k,
            2 * 2 ^ Fintype.card (Finset (Fin n)) := Finset.sum_le_sum h2
      _ = _ := by rw [Finset.sum_const, smul_eq_mul]
  simp only [card_powersetCard, card_univ, Fintype.card_fin, Fintype.card_fun,
    Fintype.card_bool] at h3
  have hpos : 0 < 2 ^ Fintype.card (Finset (Fin n)) := by positivity
  have : 2 ^ k.choose 2 ≤ n.choose k * 2 := by
    by_contra hc
    push Not at hc
    have := Nat.mul_lt_mul_of_pos_left hc hpos
    nlinarith
  omega

lemma num_bound (k : ℕ) (hk : 3 ≤ k) :
    2 * (Nat.floor ((2 : ℝ) ^ ((k : ℝ) / 2))).choose k < 2 ^ k.choose 2 := by
  set x : ℝ := (2 : ℝ) ^ ((k : ℝ) / 2) with hxdef
  have hx0 : 0 ≤ x := by positivity
  have hx2 : x ^ 2 = 2 ^ k := by
    rw [hxdef, ← Real.rpow_natCast ((2:ℝ) ^ ((k : ℝ) / 2)) 2,
      ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
    rw [show (k : ℝ) / 2 * ((2 : ℕ) : ℝ) = ((k : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  set n := Nat.floor x with hn
  have hnx : (n : ℝ) ≤ x := Nat.floor_le hx0
  have hm2 : 2 * k.choose 2 = k * (k - 1) := by
    rw [Nat.choose_two_right, mul_comm, Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self k)]
  have hkk : k * k = k * (k - 1) + k := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring
  have hf : (4 : ℝ) * 2 ^ k < ((k.factorial : ℕ) : ℝ) ^ 2 := by
    exact_mod_cast fact_sq k hk
  have hfpos : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  -- key: 2 * x^k < 2^m * k!
  have hkey : 2 * x ^ k < 2 ^ k.choose 2 * (k.factorial : ℝ) := by
    apply lt_of_pow_lt_pow_left₀ 2 (by positivity)
    have hl : (2 * x ^ k) ^ 2 = 4 * (2 ^ (k * (k - 1)) * 2 ^ k) := by
      rw [mul_pow, ← pow_mul, mul_comm k 2, pow_mul, hx2, ← pow_mul, hkk, pow_add]
      norm_num
    have hr : ((2:ℝ) ^ k.choose 2 * (k.factorial : ℝ)) ^ 2
        = 2 ^ (k * (k - 1)) * ((k.factorial : ℕ) : ℝ) ^ 2 := by
      rw [mul_pow, ← pow_mul, mul_comm (k.choose 2) 2, hm2]
    rw [hl, hr]
    have hp : (0:ℝ) < 2 ^ (k * (k - 1)) := by positivity
    nlinarith
  have hc : ((n.choose k : ℕ) : ℝ) ≤ (n : ℝ) ^ k / (k.factorial : ℝ) :=
    Nat.choose_le_pow_div k n
  have hnk : (n : ℝ) ^ k ≤ x ^ k := pow_le_pow_left₀ (Nat.cast_nonneg _) hnx k
  have : (2 : ℝ) * ((n.choose k : ℕ) : ℝ) < 2 ^ k.choose 2 := by
    calc (2 : ℝ) * ((n.choose k : ℕ) : ℝ) ≤ 2 * (x ^ k / (k.factorial : ℝ)) := by
          gcongr
          exact hc.trans (div_le_div_of_nonneg_right hnk hfpos.le)
      _ = 2 * x ^ k / (k.factorial : ℝ) := by ring
      _ < 2 ^ k.choose 2 := by rw [div_lt_iff₀ hfpos]; exact hkey
  exact_mod_cast this

end Erdos77Aux6c7f

theorem solution (k : Nat) (hk : 3 <= k) :
    Exists fun G : SimpleGraph (Fin (Nat.floor ((2 : Real) ^ ((k : Real) / 2)))) =>
      And
        (Not (Exists fun s : Finset (Fin (Nat.floor ((2 : Real) ^ ((k : Real) / 2)))) =>
          And (s.card = k) (G.IsClique s)))
        (Not (Exists fun s : Finset (Fin (Nat.floor ((2 : Real) ^ ((k : Real) / 2)))) =>
          And (s.card = k) ((Compl.compl G).IsClique s))) := by
  classical
  obtain ⟨c, hc⟩ := Erdos77Aux6c7f.bad_coloring _ k (Erdos77Aux6c7f.num_bound k hk)
  let G : SimpleGraph (Fin (Nat.floor ((2 : Real) ^ ((k : Real) / 2)))) :=
    { Adj := fun a b => a ≠ b ∧ c {a, b} = true
      symm := ⟨fun a b h => ⟨h.1.symm, by rw [Finset.pair_comm]; exact h.2⟩⟩
      loopless := ⟨fun a h => h.1 rfl⟩ }
  refine ⟨G, ?_, ?_⟩
  · rintro ⟨s, hs, hcl⟩
    obtain ⟨e, he, hce⟩ := hc s hs true
    rw [Finset.mem_powersetCard] at he
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp he.2
    have ha : a ∈ s := he.1 (by simp)
    have hb : b ∈ s := he.1 (by simp)
    exact hce (hcl ha hb hab).2
  · rintro ⟨s, hs, hcl⟩
    obtain ⟨e, he, hce⟩ := hc s hs false
    rw [Finset.mem_powersetCard] at he
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp he.2
    have ha : a ∈ s := he.1 (by simp)
    have hb : b ∈ s := he.1 (by simp)
    have h := hcl ha hb hab
    rw [SimpleGraph.compl_adj] at h
    apply h.2
    refine ⟨hab, ?_⟩
    simpa using hce
