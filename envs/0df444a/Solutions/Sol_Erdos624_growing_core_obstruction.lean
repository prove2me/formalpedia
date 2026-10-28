-- Prove2me | solution 1 for Erdos624.growing_core_obstruction
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-24T08:17:53.012709+00:00
-- url     : https://prove2.me/submissions/eb1b4862-14ce-4952-98ee-f7d2c9e145dd

import Mathlib

set_option maxHeartbeats 4000000

/-!
# Sol: growing-core / prescribed-star integral obstruction (Erdős #624 Round 8 / A5)

Honesty: does **not** settle PAIR or Erdős #624 — only a prescribed-star covering
obstruction on cores sharing a fixed (k−t)-set B.

Credit: derived from GPT 6.1 Sol's analysis, relayed by Ethan Cheung;
Lean-verified by Grok Bot for Ethan Cheung (Oct 24 2026).

Corrected: `A_t = [t(t+1)]^{2t+3} · 2^{4t(t+1)}` (Sol writeup had the 2-power in the denominator).
-/

namespace E624R8

open Finset BigOperators Function Classical

/-! ### from Basic.lean -/

/-!
# Growing-core obstruction: basic circuit lemmas (Erdős 624 / Round 8)

Credit: derived from GPT 6.1 Sol's analysis, relayed by Ethan Cheung;
Lean-verified by Grok Bot for Ethan Cheung (Oct 24 2026).
-/



/-- Ambient labelling space `𝔼 = 𝔽₂^{t-1}`. -/
abbrev E (t : ℕ) : Type := Fin (t - 1) → ZMod 2

lemma card_E (t : ℕ) : Fintype.card (E t) = 2 ^ (t - 1) := by
  simp [E, ZMod.card]

def q (t : ℕ) : ℕ := 2 ^ (t - 1)

lemma q_eq_card (t : ℕ) : q t = Fintype.card (E t) := (card_E t).symm

lemma q_pos {t : ℕ} (_ht : 1 ≤ t) : 0 < q t := by
  unfold q; exact Nat.two_pow_pos _

/-- Inclusion-minimal nonempty zero-sum support. -/
def IsCircuit {V : Type*} [DecidableEq V] {t : ℕ} (v : V → E t) (T : Finset V) : Prop :=
  T.Nonempty ∧ (∑ x ∈ T, v x) = 0 ∧
    ∀ ⦃S : Finset V⦄, S ⊆ T → S.Nonempty → S ≠ T → ∑ x ∈ S, v x ≠ 0

lemma isCircuit_minimal {V : Type*} [DecidableEq V] {t : ℕ} (v : V → E t) {T : Finset V}
    (h : IsCircuit v T) {S : Finset V} (hS : S ⊆ T) (hne : S.Nonempty)
    (hsum : ∑ x ∈ S, v x = 0) : S = T := by
  by_contra hne'
  exact h.2.2 hS hne hne' hsum

/-- Any nonempty zero-sum set contains a circuit (minimal cardinality). -/
lemma exists_circuit_of_zero_sum {V : Type*} [DecidableEq V] {t : ℕ} (v : V → E t)
    (T : Finset V) (hne : T.Nonempty) (hsum : ∑ x ∈ T, v x = 0) :
    ∃ C ⊆ T, IsCircuit v C := by
  classical
  let P : ℕ → Prop := fun n => ∃ S ⊆ T, S.Nonempty ∧ #S = n ∧ ∑ x ∈ S, v x = 0
  have hEx : ∃ n, P n := ⟨#T, T, Subset.rfl, hne, rfl, hsum⟩
  set m := Nat.find hEx with hm
  have hPm : P m := Nat.find_spec hEx
  obtain ⟨C, hCsub, hCne, hCcard, hCsum⟩ := hPm
  refine ⟨C, hCsub, hCne, hCsum, ?_⟩
  intro S hSsub hSne hSneC hSsum
  have hss : S ⊂ C := Finset.ssubset_iff_subset_ne.2 ⟨hSsub, hSneC⟩
  have hScard : #S < #C := card_lt_card hss
  have hSm : P (#S) := ⟨S, hSsub.trans hCsub, hSne, rfl, hSsum⟩
  have hmle : m ≤ #S := Nat.find_min' hEx hSm
  omega

lemma zmod2_add_self {t : ℕ} (x : E t) : x + x = (0 : E t) := by
  funext j; simp [Pi.add_apply]; generalize x j = z; fin_cases z <;> rfl

/-- `t` vectors in `𝔽₂^{t-1}` have a nonempty zero-sum subset. -/
lemma exists_zero_sum_of_card {V : Type*} [DecidableEq V] {t : ℕ}
    (_ht : 1 ≤ t) (v : V → E t) (Z : Finset V) (hZ : #Z = t) :
    ∃ A ⊆ Z, A.Nonempty ∧ ∑ a ∈ A, v a = 0 := by
  classical
  have hc : (univ : Finset (E t)).card < Z.powerset.card := by
    rw [card_univ, card_powerset, hZ, card_E]
    exact Nat.pow_lt_pow_right (by norm_num : 1 < 2) (by omega)
  obtain ⟨A, hA, B, hB, hAB, he⟩ :=
    exists_ne_map_eq_of_card_lt_of_maps_to hc (f := fun A => ∑ a ∈ A, v a)
      (fun _ _ => mem_univ _)
  rw [mem_powerset] at hA hB
  refine ⟨symmDiff A B, ?_, ?_, ?_⟩
  · intro x hx
    rw [mem_symmDiff] at hx
    rcases hx with ⟨hx, _⟩ | ⟨hx, _⟩
    · exact hA hx
    · exact hB hx
  · rw [nonempty_iff_ne_empty]; intro hc'
    exact hAB (symmDiff_eq_bot.1 hc')
  · have h1 : ∑ a ∈ A, v a = ∑ a ∈ A \ B, v a + ∑ a ∈ A ∩ B, v a := by
      rw [← sum_sdiff (inter_subset_left : A ∩ B ⊆ A), sdiff_inter_self_left]
    have h2 : ∑ a ∈ B, v a = ∑ a ∈ B \ A, v a + ∑ a ∈ A ∩ B, v a := by
      rw [inter_comm, ← sum_sdiff (inter_subset_left : B ∩ A ⊆ B), sdiff_inter_self_left]
    have hs : ∑ a ∈ symmDiff A B, v a = ∑ a ∈ A \ B, v a + ∑ a ∈ B \ A, v a := by
      rw [symmDiff_def, sup_eq_union, sum_union disjoint_sdiff_sdiff]
    have he' : ∑ a ∈ A, v a = ∑ a ∈ B, v a := he
    rw [hs]
    have hx := zmod2_add_self (t := t) (∑ a ∈ A \ B, v a + ∑ a ∈ A ∩ B, v a)
    rw [← h1] at hx
    rw [h1, h2] at he'
    calc ∑ a ∈ A \ B, v a + ∑ a ∈ B \ A, v a
        = (∑ a ∈ A \ B, v a + ∑ a ∈ A ∩ B, v a) + (∑ a ∈ B \ A, v a + ∑ a ∈ A ∩ B, v a)
            - (∑ a ∈ A ∩ B, v a + ∑ a ∈ A ∩ B, v a) := by abel
      _ = 0 := by rw [← he', ← h1, hx, zmod2_add_self (t := t), sub_zero]

/-- Every `t`-set contains a circuit. -/
lemma exists_circuit_of_card {V : Type*} [DecidableEq V] {t : ℕ}
    (ht : 1 ≤ t) (v : V → E t) (Z : Finset V) (hZ : #Z = t) :
    ∃ C ⊆ Z, IsCircuit v C := by
  obtain ⟨A, hA, hne, hsum⟩ := exists_zero_sum_of_card ht v Z hZ
  obtain ⟨C, hC, hCirc⟩ := exists_circuit_of_zero_sum v A hne hsum
  exact ⟨C, hC.trans hA, hCirc⟩

/-- Corrected threshold `A_t = [t(t+1)]^{2t+3} · 2^{4t(t+1)}`. -/
def A_t (t : ℕ) : ℕ := (t * (t + 1)) ^ (2 * t + 3) * 2 ^ (4 * t * (t + 1))

lemma A_t_eq (t : ℕ) :
    A_t t = t * (t + 1) ^ (2 * t + 3) * (t * 2 ^ (2 * t)) ^ (2 * t + 2) := by
  unfold A_t
  have h1 : (t * (t + 1)) ^ (2 * t + 3) =
      t ^ (2 * t + 3) * (t + 1) ^ (2 * t + 3) := mul_pow t (t + 1) (2 * t + 3)
  have h2 : (t * 2 ^ (2 * t)) ^ (2 * t + 2) =
      t ^ (2 * t + 2) * (2 ^ (2 * t)) ^ (2 * t + 2) := mul_pow _ _ _
  have h3 : (2 ^ (2 * t)) ^ (2 * t + 2) = 2 ^ (2 * t * (2 * t + 2)) := by
    rw [← pow_mul]
  have h4 : 2 * t * (2 * t + 2) = 4 * t * (t + 1) := by ring
  rw [h1, show 2 * t + 3 = (2 * t + 2) + 1 from by omega, pow_succ, h2, h3, h4]
  ring

/-- Reciprocal of ε: `εNat t = t · 2^{2t}`. -/
def εNat (t : ℕ) : ℕ := t * 2 ^ (2 * t)

lemma εNat_pos {t : ℕ} (ht : 1 ≤ t) : 0 < εNat t := by
  unfold εNat; have := Nat.two_pow_pos (2 * t); nlinarith

/-- For `t ≥ 2`, `t ≤ 2^t` and `t+1 ≤ 2^t`. -/
lemma t_le_two_pow {t : ℕ} (_ht : 2 ≤ t) : t ≤ 2 ^ t :=
  le_of_lt Nat.lt_two_pow_self

lemma t_succ_le_two_pow {t : ℕ} (_ht : 2 ≤ t) : t + 1 ≤ 2 ^ t := by
  -- For t ≥ 2: t+1 ≤ 2t ≤ 2^t (since 2t = t+t ≤ 2^{t-1}+2^{t-1}=2^t for t≥2, or use  t < 2^t so t+1 ≤ 2^t)
  have hlt : t < 2 ^ t := Nat.lt_two_pow_self
  exact Nat.succ_le_of_lt hlt

/-- For `t ≥ 2`, `t(t+1) ≤ 2^{2t}`. -/
lemma t_mul_t_succ_le_pow {t : ℕ} (ht : 2 ≤ t) : t * (t + 1) ≤ 2 ^ (2 * t) := by
  calc t * (t + 1) ≤ 2 ^ t * 2 ^ t := Nat.mul_le_mul (t_le_two_pow ht) (t_succ_le_two_pow ht)
    _ = 2 ^ (t + t) := by rw [← pow_add]
    _ = 2 ^ (2 * t) := by ring_nf

lemma A_t_le_pow {t : ℕ} (ht : 2 ≤ t) : A_t t ≤ 2 ^ (8 * t ^ 2 + 10 * t) := by
  have hmul := t_mul_t_succ_le_pow ht
  have h1 : (t * (t + 1)) ^ (2 * t + 3) ≤ (2 ^ (2 * t)) ^ (2 * t + 3) :=
    Nat.pow_le_pow_left hmul _
  have h2 : (2 ^ (2 * t)) ^ (2 * t + 3) = 2 ^ (2 * t * (2 * t + 3)) := by rw [← pow_mul]
  have h3 : 2 * t * (2 * t + 3) + 4 * t * (t + 1) = 8 * t ^ 2 + 10 * t := by ring
  calc A_t t
      = (t * (t + 1)) ^ (2 * t + 3) * 2 ^ (4 * t * (t + 1)) := rfl
    _ ≤ (2 ^ (2 * t)) ^ (2 * t + 3) * 2 ^ (4 * t * (t + 1)) := Nat.mul_le_mul_right _ h1
    _ = 2 ^ (2 * t * (2 * t + 3)) * 2 ^ (4 * t * (t + 1)) := by rw [h2]
    _ = 2 ^ (2 * t * (2 * t + 3) + 4 * t * (t + 1)) := by rw [← pow_add]
    _ = 2 ^ (8 * t ^ 2 + 10 * t) := by rw [h3]

lemma eight_t_sq_lt_sixteen {t : ℕ} (_ht : 2 ≤ t) :
    8 * t ^ 2 + 10 * t < 16 * (t + 1) ^ 2 := by
  have : 8 * t * t + 10 * t < 16 * t * t + 32 * t + 16 := by nlinarith
  -- rewrite both sides
  simp only [pow_two, Nat.mul_add, Nat.add_mul, Nat.mul_one] at *
  -- 16*(t+1)^2 = 16*(t^2+2t+1) = 16t^2+32t+16
  convert this using 1 <;> ring

/-- Sufficient condition: `k ≥ 16(t+1)²` implies `2^k > A_t`. -/
lemma pow_k_gt_A_t {t k : ℕ} (ht : 2 ≤ t) (hk : 16 * (t + 1) ^ 2 ≤ k) :
    A_t t < 2 ^ k := by
  have h1 : A_t t ≤ 2 ^ (8 * t ^ 2 + 10 * t) := A_t_le_pow ht
  have h2 : 8 * t ^ 2 + 10 * t < 16 * (t + 1) ^ 2 := eight_t_sq_lt_sixteen ht
  have h3 : 8 * t ^ 2 + 10 * t < k := lt_of_lt_of_le h2 hk
  have h4 : 2 ^ (8 * t ^ 2 + 10 * t) < 2 ^ k :=
    Nat.pow_lt_pow_right (by omega : 1 < 2) h3
  exact lt_of_le_of_lt h1 h4

/-! ### from CircuitProb.lean -/

/-!
# Circuit frequency bound (Sol (3)) — product weights for μ
-/



open Classical



/-- Ordered-tuple circuit predicate. -/
def IsCircuitTuple {t j : ℕ} (φ : Fin j → E t) : Prop :=
  1 ≤ j ∧ (∑ i, φ i) = (0 : E t) ∧
    ∀ S : Finset (Fin j), S.Nonempty → S ≠ univ → ∑ i ∈ S, φ i ≠ 0

def D (t : ℕ) : ℕ := 4 * t * (q t) ^ 2 * (q t - 1)
def wZero (t : ℕ) : ℕ := (4 * t * q t - 1) * (q t - 1)
def wNz (t : ℕ) : ℕ := 4 * t * q t * (q t - 1) + 1

lemma four_t_q_pos {t : ℕ} (ht : 2 ≤ t) : 1 ≤ 4 * t * q t := by
  unfold q; have : 1 ≤ 2 ^ (t - 1) := Nat.one_le_two_pow; nlinarith

lemma q_ge_two {t : ℕ} (ht : 2 ≤ t) : 2 ≤ q t := by
  unfold q
  have : 1 ≤ t - 1 := Nat.le_sub_of_add_le ht
  exact Nat.pow_le_pow_right (by decide : 0 < 2) this

lemma weight_sum (t : ℕ) (ht : 2 ≤ t) : wZero t + (q t - 1) * wNz t = D t := by
  unfold wZero wNz D
  have hpos := four_t_q_pos ht
  have hQ : 1 ≤ q t := le_trans (by omega) (q_ge_two ht)
  set Q := q t
  calc (4 * t * Q - 1) * (Q - 1) + (Q - 1) * (4 * t * Q * (Q - 1) + 1)
      = (Q - 1) * ((4 * t * Q - 1) + (4 * t * Q * (Q - 1) + 1)) := by ring
    _ = (Q - 1) * (4 * t * Q - 1 + 1 + 4 * t * Q * (Q - 1)) := by ring
    _ = (Q - 1) * (4 * t * Q + 4 * t * Q * (Q - 1)) := by rw [Nat.sub_add_cancel hpos]
    _ = (Q - 1) * (4 * t * Q * (1 + (Q - 1))) := by ring
    _ = (Q - 1) * (4 * t * Q * Q) := by rw [Nat.add_sub_cancel' hQ]
    _ = 4 * t * Q ^ 2 * (Q - 1) := by ring

def weight (t : ℕ) (z : E t) : ℕ := if z = 0 then wZero t else wNz t

lemma sum_weight (t : ℕ) (ht : 2 ≤ t) : ∑ z : E t, weight t z = D t := by
  classical
  have h := Finset.sum_erase_add (s := (univ : Finset (E t))) (f := weight t)
    (a := (0 : E t)) (mem_univ _)
  rw [← h]
  simp only [weight, ↓reduceIte]
  have hz : ∀ z ∈ univ.erase (0 : E t), (if z = 0 then wZero t else wNz t) = wNz t := by
    intro z hz; simp [mem_erase] at hz; simp [hz]
  have hc : #(univ.erase (0 : E t)) = q t - 1 := by
    rw [card_erase_of_mem (mem_univ _), card_univ, card_E]; rfl
  rw [sum_congr rfl hz, sum_const, hc, nsmul_eq_mul, Nat.cast_id, add_comm, weight_sum t ht]

def tupWeight {t j : ℕ} (φ : Fin j → E t) : ℕ := ∏ i, weight t (φ i)

lemma sum_tupWeight (t j : ℕ) (ht : 2 ≤ t) :
    ∑ φ : Fin j → E t, tupWeight (t := t) φ = D t ^ j := by
  classical
  have h := (Fintype.prod_sum (R := ℕ) (fun _ : Fin j => weight (t := t))).symm
  simpa [tupWeight, sum_weight t ht, prod_const, card_univ, Fintype.card_fin] using h

lemma εNat_eq (t : ℕ) (ht : 1 ≤ t) : εNat t = 4 * t * (q t) ^ 2 := by
  unfold εNat q
  have h1 : 2 * t = 2 * (t - 1) + 2 := by omega
  calc t * 2 ^ (2 * t)
      = t * 2 ^ (2 * (t - 1) + 2) := by rw [h1]
    _ = t * (2 ^ (2 * (t - 1)) * 2 ^ 2) := by rw [pow_add]
    _ = t * (2 ^ (2 * (t - 1)) * 4) := by rfl
    _ = t * ((2 ^ (t - 1) * 2 ^ (t - 1)) * 4) := by
        congr 1; congr 1
        rw [← pow_add]; congr 1; ring
    _ = 4 * t * (2 ^ (t - 1)) ^ 2 := by rw [← pow_two]; ring

lemma wZero_identity (t : ℕ) (ht : 2 ≤ t) :
    wZero t * q t * εNat t = D t * (εNat t - q t) := by
  have hε := εNat_eq t (by omega)
  unfold wZero D
  set Q := q t
  have hcancel : (4 * t * Q - 1) * Q = 4 * t * Q ^ 2 - Q := by
    rw [Nat.sub_mul, one_mul]; ring
  calc wZero t * Q * εNat t
      = (4 * t * Q - 1) * (Q - 1) * Q * εNat t := rfl
    _ = (4 * t * Q - 1) * (Q - 1) * Q * (4 * t * Q ^ 2) := by rw [hε]
    _ = (Q - 1) * (4 * t * Q ^ 2) * ((4 * t * Q - 1) * Q) := by ring
    _ = (Q - 1) * (4 * t * Q ^ 2) * (4 * t * Q ^ 2 - Q) := by rw [hcancel]
    _ = (4 * t * Q ^ 2 * (Q - 1)) * (4 * t * Q ^ 2 - Q) := by ring
    _ = (4 * t * Q ^ 2 * (Q - 1)) * (εNat t - Q) := by rw [hε]




/-- Circuit weight as a filtered sum. -/
noncomputable def circuitWeight (t j : ℕ) : ℕ :=
  ∑ φ ∈ univ.filter (fun φ : Fin j → E t => IsCircuitTuple (t := t) φ),
    tupWeight (t := t) φ

lemma sum_fin_one {t : ℕ} (φ : Fin 1 → E t) : ∑ i : Fin 1, φ i = φ 0 := Fin.sum_univ_one φ

/-- j = 1 case of Sol (3). -/
theorem circuit_weight_bound_j1 (t : ℕ) (ht : 2 ≤ t) :
    circuitWeight t 1 * q t * εNat t ≤ D t * (εNat t - q t) := by
  have hsum : circuitWeight t 1 = wZero t := by
    unfold circuitWeight
    have honly : univ.filter (fun φ : Fin 1 → E t => IsCircuitTuple (t := t) φ) =
        {fun _ : Fin 1 => (0 : E t)} := by
      ext φ
      simp only [mem_filter, mem_univ, true_and, mem_singleton]
      constructor
      · intro ⟨_, hsum, _⟩
        have hφ : φ 0 = 0 := by simpa [sum_fin_one] using hsum
        funext i; rw [Fin.eq_zero i, hφ]
      · intro hφ
        have hz : φ = fun _ => (0 : E t) := hφ
        refine ⟨by omega, ?_, ?_⟩
        · simp [hz, sum_fin_one]
        · intro S hSne hSneU
          have hle := card_le_univ S
          simp only [Fintype.card_fin] at hle
          have hpos := card_pos.2 hSne
          have hcard : #S = 1 := by omega
          have : S = univ := by
            refine eq_of_subset_of_card_le (subset_univ _) ?_
            simpa [card_univ, Fintype.card_fin] using hcard.symm.le
          exact (hSneU this).elim
    rw [honly, sum_singleton]
    simp [tupWeight, weight, Fin.prod_univ_one]
  rw [hsum]
  exact (wZero_identity t ht).le

/-! ### from CircuitBound.lean -/

/-!
# Uniform circuit count (Sol (3) ingredient for capacity via uniform labels)
-/




lemma circuit_first_ne {t j : ℕ} (hj : 2 ≤ j) (φ : Fin j → E t)
    (h : IsCircuitTuple (t := t) φ) : φ ⟨0, by omega⟩ ≠ 0 := by
  obtain ⟨_, _, hmin⟩ := h
  have hne : ({(⟨0, by omega⟩ : Fin j)} : Finset (Fin j)).Nonempty := singleton_nonempty _
  have hneU : ({(⟨0, by omega⟩ : Fin j)} : Finset (Fin j)) ≠ univ := by
    intro heq
    have : (1 : ℕ) = j := by
      simpa [card_singleton, card_univ, Fintype.card_fin] using congrArg card heq
    omega
  simpa using hmin {⟨0, by omega⟩} hne hneU

lemma circuit_last_eq_sum {t j : ℕ} (hj : 1 ≤ j)
    (φ : Fin j → E t) (hsum : ∑ i : Fin j, φ i = (0 : E t)) :
    φ ⟨j - 1, by omega⟩ = ∑ k : Fin (j - 1), φ ⟨k.val, by omega⟩ := by
  have hj' : j = (j - 1) + 1 := by omega
  let φ' : Fin ((j - 1) + 1) → E t := fun i => φ ⟨i.val, by omega⟩
  have hsum' : ∑ i : Fin ((j - 1) + 1), φ' i = (0 : E t) := by
    have e : ∑ i : Fin ((j - 1) + 1), φ' i = ∑ i : Fin j, φ i :=
      Fintype.sum_equiv (finCongr hj'.symm) _ _ fun _ => rfl
    exact e.trans hsum
  rw [Fin.sum_univ_castSucc (f := φ')] at hsum'
  set s := ∑ i : Fin (j - 1), φ' (Fin.castSucc i)
  set L := φ' (Fin.last (j - 1))
  have hx (x : E t) : x + x = 0 := zmod2_add_self (t := t) x
  have hsL : s + L = 0 := by simpa [s, L] using hsum'
  have hLs : L = s := by
    calc L = L + 0 := (add_zero _).symm
      _ = L + (s + s) := by rw [hx s]
      _ = (s + L) + s := by abel
      _ = 0 + s := by rw [hsL]
      _ = s := zero_add _
  show L = s
  exact hLs

lemma card_first_ne (t n : ℕ) :
    #{ψ : Fin (n + 1) → E t | ψ 0 ≠ 0} =
      (q t - 1) * q t ^ n := by
  classical
  let F : (E t) × (Fin n → E t) → (Fin (n + 1) → E t) := fun p => Fin.cons p.1 p.2
  have hinj : Injective F := by
    intro ⟨a1, r1⟩ ⟨a2, r2⟩ hp
    have h0 : a1 = a2 := by
      have := congrArg (fun f : Fin (n + 1) → E t => f 0) hp
      simpa [F, Fin.cons_zero] using this
    have ht : r1 = r2 := by
      have := congrArg (Fin.tail (α := fun _ => E t)) hp
      simpa [F, Fin.tail_cons] using this
    exact Prod.ext h0 ht
  have hcover : univ.filter (fun ψ : Fin (n + 1) → E t => ψ 0 ≠ 0) =
      ((univ.erase (0 : E t)) ×ˢ (univ : Finset (Fin n → E t))).image F := by
    ext ψ
    constructor
    · intro hψ
      have hne : ψ 0 ≠ 0 := (mem_filter.mp hψ).2
      refine mem_image.mpr ⟨(ψ 0, Fin.tail ψ), ?_, ?_⟩
      · exact mem_product.mpr ⟨mem_erase.mpr ⟨hne, mem_univ _⟩, mem_univ _⟩
      · simp only [F]; exact Fin.cons_self_tail ψ
    · intro hψ
      obtain ⟨⟨a, rest⟩, hp, hF⟩ := mem_image.mp hψ
      obtain ⟨ha, _⟩ := mem_product.mp hp
      have hne : a ≠ 0 := (mem_erase.mp ha).1
      refine mem_filter.mpr ⟨mem_univ _, ?_⟩
      have : ψ 0 = a := by rw [← hF]; simp only [F, Fin.cons_zero]
      rwa [this]
  rw [hcover, card_image_of_injective _ hinj, card_product,
      card_erase_of_mem (mem_univ (0 : E t)), card_univ, card_univ]
  simp [Fintype.card_fun, Fintype.card_fin, card_E, q]

/-- # ordered circuits of length `j≥2` ≤ `q^{j-1} - q^{j-2}`. -/
theorem circuit_card_uniform {t j : ℕ} (ht : 2 ≤ t) (hj : 2 ≤ j) :
    #{φ : Fin j → E t | IsCircuitTuple (t := t) φ} ≤
      q t ^ (j - 1) - q t ^ (j - 2) := by
  classical
  let S := univ.filter (fun φ : Fin j → E t => IsCircuitTuple (t := t) φ)
  -- Reindex Fin (j-1) as Fin ((j-2)+1)
  have hj1 : j - 1 = (j - 2) + 1 := by omega
  let Tset := univ.filter (fun ψ : Fin ((j - 2) + 1) → E t => ψ 0 ≠ 0)
  let Ψ : (Fin j → E t) → (Fin ((j - 2) + 1) → E t) := fun φ i =>
    φ ⟨i.val, by omega⟩
  have hsub : S.image Ψ ⊆ Tset := by
    intro ψ hψ
    obtain ⟨φ, hφ, rfl⟩ := mem_image.mp hψ
    exact mem_filter.mpr ⟨mem_univ _, circuit_first_ne hj φ (mem_filter.mp hφ).2⟩
  have hinj : Set.InjOn Ψ (S : Set _) := by
    intro φ hφ ψ hψ heq
    have hφc : IsCircuitTuple (t := t) φ := by
      simpa [S] using (mem_filter.mp (show φ ∈ S from hφ)).2
    have hψc : IsCircuitTuple (t := t) ψ := by
      simpa [S] using (mem_filter.mp (show ψ ∈ S from hψ)).2
    funext i
    by_cases hi : i.val < j - 1
    · have := congrFun heq ⟨i.val, by omega⟩
      simpa [Ψ] using this
    · have hiEq : i.val = j - 1 := by omega
      have hiFin : i = ⟨j - 1, by omega⟩ := Fin.ext hiEq
      rw [hiFin, circuit_last_eq_sum (by omega) φ hφc.2.1,
          circuit_last_eq_sum (by omega) ψ hψc.2.1]
      refine Fintype.sum_congr _ _ fun k => ?_
      have hk : k.val < (j - 2) + 1 := Nat.lt_of_lt_of_le k.isLt (by omega)
      exact congrFun heq ⟨k.val, hk⟩
  have hcardS : #S ≤ #Tset := by
    rw [← card_image_of_injOn hinj]
    exact card_le_card hsub
  have hcardT : #Tset = (q t - 1) * q t ^ (j - 2) := card_first_ne t (j - 2)
  have halg : (q t - 1) * q t ^ (j - 2) = q t ^ (j - 1) - q t ^ (j - 2) := by
    have hpow : q t * q t ^ (j - 2) = q t ^ (j - 1) := by
      have hs : (j - 2).succ = j - 1 := by omega
      rw [← hs, pow_succ, mul_comm]
    calc (q t - 1) * q t ^ (j - 2)
        = q t ^ (j - 2) * (q t - 1) := by ring
      _ = q t ^ (j - 2) * q t - q t ^ (j - 2) := by
          rw [Nat.mul_sub_left_distrib, mul_one]
      _ = q t ^ (j - 1) - q t ^ (j - 2) := by rw [mul_comm, hpow]
  calc #S ≤ #Tset := hcardS
    _ = (q t - 1) * q t ^ (j - 2) := hcardT
    _ = q t ^ (j - 1) - q t ^ (j - 2) := halg

/-! ### from WeightBound.lean -/

/-!
# Sol (3): `circuit_weight_bound` via hybrid coupling.
-/



set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

def uWeight (t : ℕ) : ℕ := 4 * t * q t * (q t - 1)

lemma uWeight_mul_q (t : ℕ) (_ht : 2 ≤ t) : uWeight t * q t = D t := by
  unfold uWeight D; ring

lemma wZero_le_u (t : ℕ) (_ht : 2 ≤ t) : wZero t ≤ uWeight t := by
  unfold wZero uWeight; exact Nat.mul_le_mul_right _ (Nat.sub_le _ _)

lemma u_le_wNz (t : ℕ) (_ht : 2 ≤ t) : uWeight t ≤ wNz t := by
  unfold uWeight wNz; exact Nat.le_add_right _ _

lemma weight_dev_zero (t : ℕ) (ht : 2 ≤ t) : uWeight t - wZero t = q t - 1 := by
  unfold uWeight wZero
  have hpos := four_t_q_pos ht
  set a := 4 * t * q t
  set b := q t - 1
  change a * b - (a - 1) * b = b
  have : a * b - (a - 1) * b = (a - (a - 1)) * b := by rw [← Nat.sub_mul]
  rw [this, Nat.sub_sub_self hpos, one_mul]

lemma weight_dist_le (t : ℕ) (ht : 2 ≤ t) (z : E t) :
    Nat.dist (weight t z) (uWeight t) ≤ q t - 1 := by
  by_cases hz : z = 0
  · subst hz; simp only [weight, ↓reduceIte]
    rw [Nat.dist_eq_sub_of_le (wZero_le_u t ht), weight_dev_zero t ht]
  · simp only [weight, hz, ↓reduceIte]
    rw [Nat.dist_comm, Nat.dist_eq_sub_of_le (u_le_wNz t ht)]
    have h1 : wNz t - uWeight t = 1 := by
      unfold wNz uWeight; exact Nat.add_sub_cancel_left _ _
    rw [h1]; have hq := q_ge_two ht; omega

def hybridWeight (t j r : ℕ) (φ : Fin j → E t) : ℕ :=
  ∏ i : Fin j, if i.val < r then weight t (φ i) else uWeight t

lemma hybrid_zero (t j : ℕ) (φ : Fin j → E t) :
    hybridWeight t j 0 φ = uWeight t ^ j := by
  simp [hybridWeight, prod_const, card_univ, Fintype.card_fin]

lemma hybrid_full (t j : ℕ) (φ : Fin j → E t) :
    hybridWeight t j j φ = tupWeight (t := t) φ := by
  simp [hybridWeight, tupWeight]

noncomputable def hybridCircuit (t j r : ℕ) : ℕ :=
  ∑ φ ∈ univ.filter (fun φ : Fin j → E t => IsCircuitTuple (t := t) φ),
    hybridWeight t j r φ

lemma hybridCircuit_zero_eq (t j : ℕ) :
    hybridCircuit t j 0 =
      #{φ : Fin j → E t | IsCircuitTuple (t := t) φ} * uWeight t ^ j := by
  simp [hybridCircuit, hybrid_zero, sum_const]

lemma hybridCircuit_full_eq (t j : ℕ) :
    hybridCircuit t j j = circuitWeight t j := by
  simp [hybridCircuit, circuitWeight, hybrid_full]

def restOf {t j r : ℕ} (hr : r < j) (φ : Fin j → E t) : ℕ :=
  ∏ i ∈ univ.erase (⟨r, hr⟩ : Fin j),
    if i.val < r then weight t (φ i) else uWeight t

lemma hybridWeight_eq_rest_u {t j r : ℕ} (hr : r < j) (φ : Fin j → E t) :
    hybridWeight t j r φ = restOf hr φ * uWeight t := by
  classical
  unfold hybridWeight restOf
  have h := (prod_erase_mul (univ : Finset (Fin j))
    (fun i => if i.val < r then weight t (φ i) else uWeight t)
    (mem_univ ⟨r, hr⟩)).symm
  convert h using 2; simp

lemma hybridWeight_eq_rest_w {t j r : ℕ} (hr : r < j) (φ : Fin j → E t) :
    hybridWeight t j (r + 1) φ = restOf hr φ * weight t (φ ⟨r, hr⟩) := by
  classical
  unfold hybridWeight
  have h := (prod_erase_mul (univ : Finset (Fin j))
    (fun i => if i.val < r + 1 then weight t (φ i) else uWeight t)
    (mem_univ ⟨r, hr⟩)).symm
  have hw : (if (⟨r, hr⟩ : Fin j).val < r + 1 then weight t (φ ⟨r, hr⟩) else uWeight t) =
      weight t (φ ⟨r, hr⟩) := by simp
  have hrest : ∏ i ∈ univ.erase (⟨r, hr⟩ : Fin j),
      (if i.val < r + 1 then weight t (φ i) else uWeight t) = restOf hr φ := by
    unfold restOf
    apply prod_congr rfl
    intro i hi
    have hine : i ≠ ⟨r, hr⟩ := (mem_erase.mp hi).1
    have hval : i.val ≠ r := Fin.val_ne_of_ne hine
    have hiff : (i.val < r + 1) ↔ (i.val < r) := by omega
    simp [hiff]
  calc hybridWeight t j (r + 1) φ
      = ∏ i, if i.val < r + 1 then weight t (φ i) else uWeight t := rfl
    _ = (∏ i ∈ univ.erase ⟨r, hr⟩, if i.val < r + 1 then weight t (φ i) else uWeight t) *
          (if (⟨r, hr⟩ : Fin j).val < r + 1 then weight t (φ ⟨r, hr⟩) else uWeight t) := h
    _ = restOf hr φ * weight t (φ ⟨r, hr⟩) := by rw [hrest, hw]

lemma restOf_update {t j r : ℕ} (hr : r < j) (φ : Fin j → E t) (z : E t) :
    restOf hr (Function.update φ ⟨r, hr⟩ z) = restOf hr φ := by
  unfold restOf
  apply prod_congr rfl
  intro i hi
  have hine : i ≠ ⟨r, hr⟩ := (mem_erase.mp hi).1
  simp [Function.update, if_neg hine]

lemma sum_all_hybrid (t j r : ℕ) (ht : 2 ≤ t) :
    ∑ φ : Fin j → E t, hybridWeight t j r φ = D t ^ j := by
  classical
  have hfactor (i : Fin j) :
      ∑ z : E t, (if i.val < r then weight t z else uWeight t) = D t := by
    by_cases hi : i.val < r
    · simp [hi, sum_weight t ht]
    · have hsum : ∑ _z : E t, uWeight t = Fintype.card (E t) * uWeight t := by
        simp [sum_const, card_univ]
      simp only [hi, ↓reduceIte]
      rw [hsum, card_E]
      change q t * uWeight t = D t
      rw [mul_comm, uWeight_mul_q t ht]
  have := (Fintype.prod_sum (R := ℕ)
    (fun i : Fin j => fun z => if i.val < r then weight t z else uWeight t)).symm
  simpa [hybridWeight, hfactor, prod_const, card_univ, Fintype.card_fin] using this

lemma sum_restOf {t j r : ℕ} (hr : r < j) (ht : 2 ≤ t) :
    ∑ φ : Fin j → E t, restOf hr φ = q t * D t ^ (j - 1) := by
  classical
  have hhyb := sum_all_hybrid t j r ht
  have hrew : ∑ φ : Fin j → E t, hybridWeight t j r φ =
      (∑ φ : Fin j → E t, restOf hr φ) * uWeight t := by
    calc ∑ φ, hybridWeight t j r φ
        = ∑ φ, (restOf hr φ * uWeight t) := by
          apply sum_congr rfl; intro φ _; rw [hybridWeight_eq_rest_u hr]
      _ = ∑ φ, (uWeight t * restOf hr φ) := by simp_rw [mul_comm]
      _ = uWeight t * ∑ φ, restOf hr φ := (mul_sum _ _ _).symm
      _ = (∑ φ, restOf hr φ) * uWeight t := mul_comm _ _
  rw [hrew] at hhyb
  have hUpos : 0 < uWeight t := by
    unfold uWeight
    have hq := q_ge_two ht
    have h1 : 0 < 4 * t * q t := lt_of_lt_of_le (by omega : 0 < 1) (four_t_q_pos ht)
    have h2 : 0 < q t - 1 := Nat.sub_pos_of_lt hq
    exact Nat.mul_pos h1 h2
  have hD : D t ^ j = (q t * D t ^ (j - 1)) * uWeight t := by
    have hj1 : 1 ≤ j := by omega
    calc D t ^ j
        = D t ^ (j - 1 + 1) := by rw [Nat.sub_add_cancel hj1]
      _ = D t ^ (j - 1) * D t := pow_succ _ _
      _ = D t ^ (j - 1) * (uWeight t * q t) := by rw [← uWeight_mul_q t ht]
      _ = (q t * D t ^ (j - 1)) * uWeight t := by ring
  rw [hD] at hhyb
  exact Nat.eq_of_mul_eq_mul_right hUpos hhyb

lemma circuit_unique_update {t j r : ℕ} (hr : r < j) (φ : Fin j → E t) :
    #{z : E t | IsCircuitTuple (t := t) (Function.update φ ⟨r, hr⟩ z)} ≤ 1 := by
  classical
  apply card_le_one.mpr
  intro z1 hz1 z2 hz2
  have s1 := (mem_filter.mp hz1).2.2.1
  have s2 := (mem_filter.mp hz2).2.2.1
  have form (z : E t) :
      ∑ i, Function.update φ ⟨r, hr⟩ z i =
        z + ∑ i ∈ univ.erase ⟨r, hr⟩, φ i := by
    have h := (sum_erase_add (univ : Finset (Fin j))
      (Function.update φ ⟨r, hr⟩ z) (mem_univ ⟨r, hr⟩)).symm
    have hz : Function.update φ ⟨r, hr⟩ z ⟨r, hr⟩ = z := by simp [Function.update]
    have hrest : ∑ i ∈ univ.erase ⟨r, hr⟩, Function.update φ ⟨r, hr⟩ z i =
        ∑ i ∈ univ.erase ⟨r, hr⟩, φ i := by
      apply sum_congr rfl; intro i hi
      have hine : i ≠ ⟨r, hr⟩ := (mem_erase.mp hi).1
      simp [Function.update, if_neg hine]
    calc ∑ i, Function.update φ ⟨r, hr⟩ z i
        = ∑ i ∈ univ.erase ⟨r, hr⟩, Function.update φ ⟨r, hr⟩ z i +
            Function.update φ ⟨r, hr⟩ z ⟨r, hr⟩ := h
      _ = ∑ i ∈ univ.erase ⟨r, hr⟩, φ i + z := by rw [hrest, hz]
      _ = z + ∑ i ∈ univ.erase ⟨r, hr⟩, φ i := add_comm _ _
  have solve_z (z : E t) (hs : ∑ i, Function.update φ ⟨r, hr⟩ z i = 0) :
      z = ∑ i ∈ univ.erase ⟨r, hr⟩, φ i := by
    have h0 : z + ∑ i ∈ univ.erase ⟨r, hr⟩, φ i = 0 := (form z) ▸ hs
    have hs2 := zmod2_add_self (t := t) (∑ i ∈ univ.erase ⟨r, hr⟩, φ i)
    calc z = z + 0 := (add_zero _).symm
      _ = z + ((∑ i ∈ univ.erase ⟨r, hr⟩, φ i) + (∑ i ∈ univ.erase ⟨r, hr⟩, φ i)) := by rw [hs2]
      _ = (z + ∑ i ∈ univ.erase ⟨r, hr⟩, φ i) + ∑ i ∈ univ.erase ⟨r, hr⟩, φ i := by ac_rfl
      _ = 0 + ∑ i ∈ univ.erase ⟨r, hr⟩, φ i := by rw [h0]
      _ = ∑ i ∈ univ.erase ⟨r, hr⟩, φ i := zero_add _
  exact (solve_z z1 s1).trans (solve_z z2 s2).symm


lemma sum_rest_slice {t j r : ℕ} (hr : r < j) (ht : 2 ≤ t) (z0 : E t) :
    ∑ φ ∈ univ.filter (fun φ : Fin j → E t => φ ⟨r, hr⟩ = z0), restOf hr φ =
      D t ^ (j - 1) := by
  classical
  let slice : Finset (Fin j → E t) :=
    univ.filter (fun φ : Fin j → E t => φ ⟨r, hr⟩ = z0)
  let g : (Fin j → E t) → (Fin j → E t) := fun φ => Function.update φ ⟨r, hr⟩ z0
  have hg : ∀ φ ∈ (univ : Finset (Fin j → E t)), g φ ∈ slice := by
    intro φ _; simp [slice, g, Function.update, mem_filter]
  have hfiber :=
    sum_fiberwise_of_maps_to (s := (univ : Finset (Fin j → E t))) (t := slice)
      (g := g) hg (fun φ => restOf hr (g φ))
  have hleft : ∑ φ : Fin j → E t, restOf hr (g φ) =
      q t * D t ^ (j - 1) := by
    simp_rw [show ∀ φ, restOf hr (g φ) = restOf hr φ from fun φ => restOf_update hr φ z0]
    exact sum_restOf hr ht
  have hcard (ψ : Fin j → E t) (hψ : ψ ∈ slice) :
      #{φ : Fin j → E t | g φ = ψ} = q t := by
    have hψr : ψ ⟨r, hr⟩ = z0 := by simp [slice, mem_filter] at hψ; exact hψ
    let e : E t ≃ {φ // g φ = ψ} :=
      { toFun := fun z => ⟨Function.update ψ ⟨r, hr⟩ z, by
          funext i; by_cases hi : i = ⟨r, hr⟩
          · subst hi; simp [g, Function.update, hψr]
          · simp [g, Function.update, if_neg hi]⟩
        invFun := fun p => p.1 ⟨r, hr⟩
        left_inv := fun z => by simp [Function.update]
        right_inv := fun ⟨φ, hφ⟩ => by
          apply Subtype.ext
          funext i
          by_cases hi : i = ⟨r, hr⟩
          · subst hi; simp [Function.update]
          · have hoff : φ i = ψ i := by
              have := congr_fun hφ i
              simpa [g, Function.update, if_neg hi] using this
            simp [Function.update, if_neg hi, hoff] }
    have hc := (Fintype.card_congr e).symm
    rw [Fintype.card_subtype, card_E] at hc
    simpa [q] using hc
  have hinner : ∀ ψ ∈ slice,
      (∑ φ ∈ univ.filter (fun φ => g φ = ψ), restOf hr (g φ)) =
        q t * restOf hr ψ := by
    intro ψ hψ
    have hconst : ∀ φ ∈ univ.filter (fun φ => g φ = ψ),
        restOf hr (g φ) = restOf hr ψ := by
      intro φ hφ; rw [(mem_filter.mp hφ).2]
    rw [sum_congr rfl hconst, sum_const, hcard ψ hψ, nsmul_eq_mul, Nat.cast_id]
  have : q t * ∑ ψ ∈ slice, restOf hr ψ = q t * D t ^ (j - 1) := by
    calc q t * ∑ ψ ∈ slice, restOf hr ψ
        = ∑ ψ ∈ slice, (q t * restOf hr ψ) := by rw [mul_sum]
      _ = ∑ ψ ∈ slice, ∑ φ ∈ univ.filter (fun φ => g φ = ψ), restOf hr (g φ) := by
          apply sum_congr rfl; intro ψ hψ; exact (hinner ψ hψ).symm
      _ = ∑ φ ∈ (univ : Finset (Fin j → E t)), restOf hr (g φ) := by
          simpa using hfiber
      _ = q t * D t ^ (j - 1) := by simpa using hleft
  have hqpos : 0 < q t := lt_of_lt_of_le (by omega : 0 < 2) (q_ge_two ht)
  exact Nat.eq_of_mul_eq_mul_left hqpos this



lemma sum_rest_circuits_le {t j r : ℕ} (hr : r < j) (ht : 2 ≤ t) :
    (∑ φ ∈ univ.filter (fun φ : Fin j → E t => IsCircuitTuple (t := t) φ),
      restOf hr φ) ≤ D t ^ (j - 1) := by
  classical
  let S := univ.filter (fun φ : Fin j → E t => IsCircuitTuple (t := t) φ)
  let F : (Fin j → E t) → (Fin j → E t) := fun φ => Function.update φ ⟨r, hr⟩ 0
  have hinj : Set.InjOn F (S : Set (Fin j → E t)) := by
    intro φ1 h1 φ2 h2 heq
    have hoff : ∀ i ≠ ⟨r, hr⟩, φ1 i = φ2 i := by
      intro i hi
      have : F φ1 i = F φ2 i := by rw [heq]
      simpa [F, Function.update, if_neg hi] using this
    have hφ1 : IsCircuitTuple (t := t) φ1 := (mem_filter.mp (show φ1 ∈ S from h1)).2
    have hφ2 : IsCircuitTuple (t := t) φ2 := (mem_filter.mp (show φ2 ∈ S from h2)).2
    have heqφ : Function.update φ2 ⟨r, hr⟩ (φ1 ⟨r, hr⟩) = φ1 := by
      funext i; by_cases hi : i = ⟨r, hr⟩
      · subst hi; simp [Function.update]
      · simp [Function.update, if_neg hi, hoff i hi]
    have hz1 : IsCircuitTuple (t := t) (Function.update φ2 ⟨r, hr⟩ (φ1 ⟨r, hr⟩)) := by
      rwa [heqφ]
    have hz2 : IsCircuitTuple (t := t) (Function.update φ2 ⟨r, hr⟩ (φ2 ⟨r, hr⟩)) := by
      rw [Function.update_eq_self]; exact hφ2
    have mem1 : φ1 ⟨r, hr⟩ ∈
        univ.filter (fun z => IsCircuitTuple (t := t) (Function.update φ2 ⟨r, hr⟩ z)) := by
      refine mem_filter.mpr ⟨mem_univ _, hz1⟩
    have mem2 : φ2 ⟨r, hr⟩ ∈
        univ.filter (fun z => IsCircuitTuple (t := t) (Function.update φ2 ⟨r, hr⟩ z)) := by
      refine mem_filter.mpr ⟨mem_univ _, hz2⟩
    have hzeq : φ1 ⟨r, hr⟩ = φ2 ⟨r, hr⟩ :=
      (card_le_one.mp (circuit_unique_update hr φ2)) _ mem1 _ mem2
    funext i
    by_cases hi : i = ⟨r, hr⟩
    · subst hi; exact hzeq
    · exact hoff i hi
  have himg_sub : S.image F ⊆ univ.filter (fun φ : Fin j → E t => φ ⟨r, hr⟩ = 0) := by
    intro ψ hψ
    obtain ⟨φ, _, rfl⟩ := mem_image.mp hψ
    simp [mem_filter, F, Function.update]
  have hsum_img : ∑ φ ∈ S, restOf hr φ = ∑ ψ ∈ S.image F, restOf hr ψ := by
    calc ∑ φ ∈ S, restOf hr φ
        = ∑ φ ∈ S, restOf hr (F φ) := by
          apply sum_congr rfl; intro φ _; exact (restOf_update hr φ 0).symm
      _ = ∑ ψ ∈ S.image F, restOf hr ψ :=
          (Finset.sum_image (f := restOf hr) (g := F) hinj).symm
  calc ∑ φ ∈ S, restOf hr φ
      = ∑ ψ ∈ S.image F, restOf hr ψ := hsum_img
    _ ≤ ∑ ψ ∈ univ.filter (fun φ => φ ⟨r, hr⟩ = (0 : E t)), restOf hr ψ :=
        sum_le_sum_of_subset_of_nonneg himg_sub (fun _ _ _ => Nat.zero_le _)
    _ = D t ^ (j - 1) := sum_rest_slice hr ht 0

lemma dist_mul (c a b : ℕ) : Nat.dist (c * a) (c * b) = c * Nat.dist a b := by
  simp only [Nat.dist]
  rcases le_total a b with h | h
  · have hc : c * a ≤ c * b := Nat.mul_le_mul_left c h
    rw [Nat.sub_eq_zero_of_le h, Nat.sub_eq_zero_of_le hc, zero_add, zero_add,
        Nat.mul_sub]
  · have hc : c * b ≤ c * a := Nat.mul_le_mul_left c h
    rw [Nat.sub_eq_zero_of_le h, Nat.sub_eq_zero_of_le hc, add_zero, add_zero,
        Nat.mul_sub]

lemma dist_weighted_sum {α : Type*} (s : Finset α) (a f g : α → ℕ) :
    Nat.dist (∑ x ∈ s, a x * f x) (∑ x ∈ s, a x * g x) ≤
      ∑ x ∈ s, a x * Nat.dist (f x) (g x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih =>
    simp only [sum_insert hx]
    have htri : Nat.dist (a x * f x + ∑ y ∈ s, a y * f y)
        (a x * g x + ∑ y ∈ s, a y * g y) ≤
        Nat.dist (a x * f x) (a x * g x) +
          Nat.dist (∑ y ∈ s, a y * f y) (∑ y ∈ s, a y * g y) := by
      simp only [Nat.dist]; omega
    have hmid : Nat.dist (a x * f x) (a x * g x) +
          Nat.dist (∑ y ∈ s, a y * f y) (∑ y ∈ s, a y * g y) ≤
        a x * Nat.dist (f x) (g x) + ∑ y ∈ s, a y * Nat.dist (f y) (g y) := by
      rw [dist_mul]; exact Nat.add_le_add_left ih _
    exact le_trans htri hmid

lemma hybrid_step_le (t j r : ℕ) (ht : 2 ≤ t) (hr : r < j) :
    Nat.dist (hybridCircuit t j (r + 1)) (hybridCircuit t j r) ≤
      (q t - 1) * D t ^ (j - 1) := by
  classical
  let S := univ.filter (fun φ : Fin j → E t => IsCircuitTuple (t := t) φ)
  have hH1 : hybridCircuit t j (r + 1) =
      ∑ φ ∈ S, restOf hr φ * weight t (φ ⟨r, hr⟩) := by
    apply sum_congr rfl; intro φ _; exact hybridWeight_eq_rest_w hr φ
  have hH0 : hybridCircuit t j r =
      ∑ φ ∈ S, restOf hr φ * uWeight t := by
    apply sum_congr rfl; intro φ _; exact hybridWeight_eq_rest_u hr φ
  have hdist : Nat.dist (hybridCircuit t j (r + 1)) (hybridCircuit t j r) ≤
      ∑ φ ∈ S, restOf hr φ * Nat.dist (weight t (φ ⟨r, hr⟩)) (uWeight t) := by
    rw [hH1, hH0]
    exact dist_weighted_sum S (restOf hr)
      (fun φ => weight t (φ ⟨r, hr⟩)) (fun _ => uWeight t)
  calc Nat.dist (hybridCircuit t j (r + 1)) (hybridCircuit t j r)
      ≤ ∑ φ ∈ S, restOf hr φ * Nat.dist (weight t (φ ⟨r, hr⟩)) (uWeight t) := hdist
    _ ≤ ∑ φ ∈ S, restOf hr φ * (q t - 1) := by
        apply sum_le_sum; intro φ _; exact Nat.mul_le_mul_left _ (weight_dist_le t ht _)
    _ = (q t - 1) * ∑ φ ∈ S, restOf hr φ := by
        simp_rw [mul_comm (restOf hr _) (q t - 1)]; rw [← mul_sum]
    _ ≤ (q t - 1) * D t ^ (j - 1) := Nat.mul_le_mul_left _ (sum_rest_circuits_le hr ht)


lemma hybrid_telescope (t j : ℕ) (ht : 2 ≤ t) (hj : 1 ≤ j) :
    circuitWeight t j ≤
      hybridCircuit t j 0 + j * (q t - 1) * D t ^ (j - 1) := by
  have hstep : ∀ r, r < j →
      Nat.dist (hybridCircuit t j (r + 1)) (hybridCircuit t j r) ≤
        (q t - 1) * D t ^ (j - 1) := fun r hr => hybrid_step_le t j r ht hr
  have hdist : Nat.dist (hybridCircuit t j j) (hybridCircuit t j 0) ≤
      j * ((q t - 1) * D t ^ (j - 1)) := by
    suffices ∀ k ≤ j, Nat.dist (hybridCircuit t j k) (hybridCircuit t j 0) ≤
        k * ((q t - 1) * D t ^ (j - 1)) by exact this j le_rfl
    intro k hk
    induction k with
    | zero => simp [Nat.dist_self]
    | succ k ih =>
      have hk' : k < j := by omega
      have ih' := ih (by omega)
      have hs := hstep k hk'
      calc Nat.dist (hybridCircuit t j (k + 1)) (hybridCircuit t j 0)
          ≤ Nat.dist (hybridCircuit t j (k + 1)) (hybridCircuit t j k) +
              Nat.dist (hybridCircuit t j k) (hybridCircuit t j 0) :=
            Nat.dist.triangle_inequality _ _ _
        _ ≤ (q t - 1) * D t ^ (j - 1) + k * ((q t - 1) * D t ^ (j - 1)) :=
            Nat.add_le_add hs ih'
        _ = (k + 1) * ((q t - 1) * D t ^ (j - 1)) := by ring
  rw [← hybridCircuit_full_eq]
  cases Nat.le_total (hybridCircuit t j j) (hybridCircuit t j 0) with
  | inl hle => exact le_trans hle (Nat.le_add_right _ _)
  | inr hle =>
    have hd : Nat.dist (hybridCircuit t j j) (hybridCircuit t j 0) =
        hybridCircuit t j j - hybridCircuit t j 0 := by
      rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hle]
    have h := hdist
    rw [hd] at h
    have : hybridCircuit t j j ≤ hybridCircuit t j 0 +
        j * ((q t - 1) * D t ^ (j - 1)) := by omega
    convert this using 2; ring


lemma D_eq_ε_mul (t : ℕ) (ht : 2 ≤ t) : D t = εNat t * (q t - 1) := by
  have hε := εNat_eq t (by omega)
  rw [hε]; unfold D; ring

lemma uWeight_pow_mul_q_pow (t j : ℕ) (ht : 2 ≤ t) :
    uWeight t ^ j * q t ^ j = D t ^ j := by
  have h := uWeight_mul_q t ht
  calc uWeight t ^ j * q t ^ j = (uWeight t * q t) ^ j := (mul_pow _ _ _).symm
    _ = D t ^ j := by rw [h]

lemma key_fac_ineq {t j : ℕ} (ht : 2 ≤ t) (hj : j ≤ t) (hq : 2 ≤ q t)
    (hε : εNat t = 4 * t * q t ^ 2) :
    (q t - 1) * εNat t + j * q t ^ 2 ≤ (εNat t - q t) * q t := by
  have hq1 : 1 ≤ q t := by omega
  have hεge : q t ≤ εNat t := by
    rw [hε]
    have : 1 ≤ 4 * t * q t := by nlinarith
    calc q t = 1 * q t := (one_mul _).symm
      _ ≤ (4 * t * q t) * q t := Nat.mul_le_mul_right _ this
      _ = 4 * t * q t ^ 2 := by ring
  have hj4 : j + 1 ≤ 4 * t := by omega
  have hkey : (j + 1) * q t ^ 2 ≤ εNat t := by
    rw [hε]; exact Nat.mul_le_mul_right _ hj4
  zify [hq1, hεge]
  have hkeyZ : ((j + 1 : ℕ) : ℤ) * (q t : ℤ) ^ 2 ≤ (εNat t : ℤ) := by
    exact_mod_cast hkey
  have hj1Z : ((j + 1 : ℕ) : ℤ) = (j : ℤ) + 1 := by exact_mod_cast rfl
  nlinarith

lemma pow_sub_two_mul (q j : ℕ) (hj2 : 2 ≤ j) :
    q ^ (j - 2) * q ^ 2 = q ^ j := by
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 2 := ⟨j - 2, by omega⟩
  simp [pow_add]

lemma pow_sub_one_mul (D j : ℕ) (hj1 : 1 ≤ j) :
    D ^ (j - 1) * D = D ^ j := by
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  simp [pow_succ]

lemma gap_pow_factor (q j : ℕ) (hj2 : 2 ≤ j) (hqpos : 0 < q) :
    q ^ (j - 1) - q ^ (j - 2) = q ^ (j - 2) * (q - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 2 := ⟨j - 2, by omega⟩
  have hle : q ^ m ≤ q ^ m * q := Nat.le_mul_of_pos_right _ hqpos
  have hm1 : m + 2 - 1 = m + 1 := by omega
  have hm2 : m + 2 - 2 = m := by omega
  rw [hm1, hm2, pow_succ]
  calc q ^ m * q - q ^ m
      = q ^ m * q - q ^ m * 1 := by rw [mul_one]
    _ = q ^ m * (q - 1) := (Nat.mul_sub (q ^ m) q 1).symm

/-- Sol (3). -/
theorem circuit_weight_bound {t j : ℕ} (ht : 2 ≤ t) (hj1 : 1 ≤ j) (hj : j ≤ t) :
    circuitWeight t j * q t * εNat t ≤ D t ^ j * (εNat t - q t) := by
  obtain rfl | _ := hj1.eq_or_lt
  · simpa [pow_one] using circuit_weight_bound_j1 t ht
  · have hj2 : 2 ≤ j := by omega
    have hq := q_ge_two ht
    have hε := εNat_eq t (by omega)
    have htel := hybrid_telescope t j ht (by omega)
    have h0 : hybridCircuit t j 0 ≤
        (q t ^ (j - 1) - q t ^ (j - 2)) * uWeight t ^ j := by
      rw [hybridCircuit_zero_eq]
      exact Nat.mul_le_mul_right _ (circuit_card_uniform ht hj2)
    have hmain : circuitWeight t j ≤
        (q t ^ (j - 1) - q t ^ (j - 2)) * uWeight t ^ j +
          j * (q t - 1) * D t ^ (j - 1) :=
      le_trans htel (Nat.add_le_add_right h0 _)
    have hqpos : 0 < q t := by omega
    have hDε : D t = εNat t * (q t - 1) := D_eq_ε_mul t ht
    have hgapN := gap_pow_factor (q t) j hj2 hqpos
    set A := (q t ^ (j - 1) - q t ^ (j - 2)) * uWeight t ^ j with hA
    set B := j * (q t - 1) * D t ^ (j - 1) with hB
    have hAq2 : A * q t ^ 2 = (q t - 1) * D t ^ j := by
      rw [hA, hgapN]
      calc q t ^ (j - 2) * (q t - 1) * uWeight t ^ j * q t ^ 2
          = (q t - 1) * uWeight t ^ j * (q t ^ (j - 2) * q t ^ 2) := by ring
        _ = (q t - 1) * uWeight t ^ j * q t ^ j := by rw [pow_sub_two_mul _ j hj2]
        _ = (q t - 1) * (uWeight t ^ j * q t ^ j) := by ring
        _ = (q t - 1) * D t ^ j := by rw [uWeight_pow_mul_q_pow t j ht]
    have hBq2ε : B * (q t ^ 2 * εNat t) = j * q t ^ 2 * D t ^ j := by
      rw [hB]
      calc j * (q t - 1) * D t ^ (j - 1) * (q t ^ 2 * εNat t)
          = j * q t ^ 2 * D t ^ (j - 1) * (εNat t * (q t - 1)) := by ring
        _ = j * q t ^ 2 * D t ^ (j - 1) * D t := by rw [← hDε]
        _ = j * q t ^ 2 * (D t ^ (j - 1) * D t) := by ring
        _ = j * q t ^ 2 * D t ^ j := by rw [pow_sub_one_mul _ j (by omega)]
    have hfac := key_fac_ineq (t := t) (j := j) ht hj hq hε
    have hcleared : (A + B) * (q t * εNat t) * q t ≤
        D t ^ j * (εNat t - q t) * q t := by
      have : (A + B) * (q t * εNat t) * q t =
          A * q t ^ 2 * εNat t + B * (q t ^ 2 * εNat t) := by ring
      rw [this, hAq2, hBq2ε]
      calc (q t - 1) * D t ^ j * εNat t + j * q t ^ 2 * D t ^ j
          = D t ^ j * ((q t - 1) * εNat t + j * q t ^ 2) := by ring
        _ ≤ D t ^ j * ((εNat t - q t) * q t) := Nat.mul_le_mul_left _ hfac
        _ = D t ^ j * (εNat t - q t) * q t := by ring
    have hAB : (A + B) * q t * εNat t ≤ D t ^ j * (εNat t - q t) :=
      Nat.le_of_mul_le_mul_right (by convert hcleared using 1 <;> ring) hqpos
    have : circuitWeight t j * q t * εNat t ≤ (A + B) * q t * εNat t :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hmain)
    exact le_trans this hAB

/-! ### from Moment.lean -/


/-!
# Finite high-moment counting ingredients (Sol (5))
-/



/-- `#` of maps `Fin d → Fin n` with image cardinality `j` is ≤ `n^j * j^d`. -/
lemma card_fixed_image_size_le (n j d : ℕ) :
    #{f : Fin d → Fin n | #(univ.image f) = j} ≤ n ^ j * j ^ d := by
  classical
  let Ψ : (Fin j → Fin n) × (Fin d → Fin j) → (Fin d → Fin n) := fun p => p.1 ∘ p.2
  have hcover : (univ.filter (fun f : Fin d → Fin n => #(univ.image f) = j)) ⊆
      univ.image Ψ := by
    intro f hf
    simp only [mem_filter, mem_univ, true_and] at hf
    simp only [mem_image, mem_univ, true_and]
    set im := univ.image f
    have hc : #im = j := by simpa [im] using hf
    let e : im ≃ Fin j := Finset.equivFinOfCardEq hc
    refine ⟨(fun i => (e.symm i).1, fun x => e ⟨f x, by simp [im]⟩), ?_⟩
    funext x
    change (e.symm (e ⟨f x, _⟩)).1 = f x
    simp
  have hle : #{f : Fin d → Fin n | #(univ.image f) = j} ≤ #(univ.image Ψ) := by
    simpa using card_le_card hcover
  refine hle.trans ((card_image_le).trans ?_)
  simp [card_univ, Fintype.card_prod, Fintype.card_fin]

lemma image_card_pos {n s : ℕ} (_hs : 1 ≤ s) (f : Fin (2 * s) → Fin n) :
    0 < #(univ.image f) := by
  let x : Fin (2 * s) := ⟨0, by omega⟩
  exact card_pos.2 ⟨f x, mem_image_of_mem _ (mem_univ _)⟩

/-- Maps of length `2s` using ≤ `s` distinct values: ≤ `s^{2s+1} n^s`. -/
lemma card_few_distinct_moment (n s : ℕ) (hs : 1 ≤ s) :
    #{f : Fin (2 * s) → Fin n | #(univ.image f) ≤ s} ≤ s ^ (2 * s + 1) * n ^ s := by
  classical
  have hpartition :
      univ.filter (fun f : Fin (2 * s) → Fin n => #(univ.image f) ≤ s) =
        (Icc 1 s).biUnion (fun j => univ.filter (fun f => #(univ.image f) = j)) := by
    ext f
    simp only [mem_filter, mem_univ, true_and, mem_biUnion, mem_Icc]
    constructor
    · intro hf
      refine ⟨#(univ.image f), ⟨Nat.succ_le_of_lt (image_card_pos hs f), hf⟩, rfl⟩
    · intro ⟨j, ⟨_, hjs⟩, hf⟩
      omega
  have hdisj : (↑(Icc 1 s) : Set ℕ).PairwiseDisjoint
      (fun j => univ.filter (fun f : Fin (2 * s) → Fin n => #(univ.image f) = j)) := by
    intro x _hx y _hy hxy
    change Disjoint
      (univ.filter (fun f : Fin (2 * s) → Fin n => #(univ.image f) = x))
      (univ.filter (fun f : Fin (2 * s) → Fin n => #(univ.image f) = y))
    rw [disjoint_filter]
    intro f _ hf1 hf2
    exact hxy (Eq.trans hf1.symm hf2)
  have hcard :
      #{f : Fin (2 * s) → Fin n | #(univ.image f) ≤ s} =
        ∑ j ∈ Icc 1 s, #{f : Fin (2 * s) → Fin n | #(univ.image f) = j} := by
    calc #{f : Fin (2 * s) → Fin n | #(univ.image f) ≤ s}
        = #((Icc 1 s).biUnion (fun j => univ.filter (fun f => #(univ.image f) = j))) := by
          simpa using congrArg card hpartition
      _ = ∑ j ∈ Icc 1 s, #(univ.filter (fun f => #(univ.image f) = j)) := card_biUnion hdisj
      _ = ∑ j ∈ Icc 1 s, #{f : Fin (2 * s) → Fin n | #(univ.image f) = j} := by rfl
  rw [hcard]
  have hstep1 : ∑ j ∈ Icc 1 s, #{f : Fin (2 * s) → Fin n | #(univ.image f) = j} ≤
      ∑ j ∈ Icc 1 s, n ^ j * j ^ (2 * s) :=
    sum_le_sum fun j _ => by simpa using card_fixed_image_size_le n j (2 * s)
  have hstep2 : ∑ j ∈ Icc 1 s, n ^ j * j ^ (2 * s) ≤ ∑ j ∈ Icc 1 s, n ^ s * s ^ (2 * s) := by
    apply sum_le_sum; intro j hj
    obtain ⟨hj1, hjs⟩ := mem_Icc.mp hj
    refine Nat.mul_le_mul ?_ (Nat.pow_le_pow_left hjs _)
    cases n with
    | zero =>
      have hjpos : 0 < j := hj1
      have hspos : 0 < s := hs
      simp [Nat.zero_pow hjpos, Nat.zero_pow hspos]
    | succ n =>
      exact Nat.pow_le_pow_right (Nat.zero_lt_succ _) hjs
  have hIcc : #(Icc 1 s) = s := by rw [Nat.card_Icc]; omega
  have hstep3a : ∑ j ∈ Icc 1 s, n ^ s * s ^ (2 * s) =
      #(Icc 1 s) * (n ^ s * s ^ (2 * s)) := by
    rw [sum_const, nsmul_eq_mul, Nat.cast_id]
  have hstep3 : ∑ j ∈ Icc 1 s, n ^ s * s ^ (2 * s) = s * (n ^ s * s ^ (2 * s)) := by
    rw [hstep3a, hIcc]
  have hstep4 : s * (n ^ s * s ^ (2 * s)) = s ^ (2 * s + 1) * n ^ s := by
    rw [pow_succ']; ring
  exact (hstep1.trans hstep2).trans (hstep3.trans hstep4).le

/-! ## Centered coordinates -/

noncomputable def centerZ {σ : Type*} [Fintype σ] (f : σ → Bool) : σ → ℚ :=
  fun x => (if f x then (1 : ℚ) else 0) -
    ((#{y : σ | f y = true}) : ℚ) / Fintype.card σ

lemma centerZ_mean {σ : Type*} [Fintype σ] [Nonempty σ] (f : σ → Bool) :
    ∑ x : σ, centerZ f x = 0 := by
  classical
  set μ : ℚ := (#{y : σ | f y = true} : ℚ) / Fintype.card σ
  have hsum : ∑ x : σ, (if f x then (1 : ℚ) else 0) = (#{y : σ | f y = true} : ℚ) := by
    simp [sum_boole]
  have hμsum : ∑ x : σ, μ = (Fintype.card σ : ℚ) * μ := by
    rw [sum_const, nsmul_eq_mul]; simp [card_univ]
  calc ∑ x : σ, centerZ f x
      = ∑ x : σ, ((if f x then (1 : ℚ) else 0) - μ) := rfl
    _ = (∑ x : σ, (if f x then (1 : ℚ) else 0)) - ∑ x : σ, μ := sum_sub_distrib _ _
    _ = (#{y : σ | f y = true} : ℚ) - (Fintype.card σ : ℚ) * μ := by rw [hsum, hμsum]
    _ = μ * Fintype.card σ - Fintype.card σ * μ := by simp only [μ]; field_simp
    _ = 0 := by ring

lemma centerZ_abs_le_one {σ : Type*} [Fintype σ] [Nonempty σ] (f : σ → Bool) (x : σ) :
    |centerZ f x| ≤ 1 := by
  set μ : ℚ := (#{y : σ | f y = true} : ℚ) / Fintype.card σ with hμ
  have hμ0 : 0 ≤ μ := by positivity
  have hcard : (#{y : σ | f y = true} : ℚ) ≤ Fintype.card σ := by
    exact_mod_cast (card_filter_le (univ : Finset σ) _)
  have hμ1 : μ ≤ 1 := by
    have hden : (0 : ℚ) < Fintype.card σ := Nat.cast_pos.mpr Fintype.card_pos
    exact (div_le_one hden).2 hcard
  simp only [centerZ, ← hμ]
  cases hx : f x <;> simp [abs_le] <;> constructor <;> linarith

lemma sum_update_center {σ : Type*} [Fintype σ] [Nonempty σ]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : σ → Bool) (i0 : ι) (g : (ι → σ) → ℚ)
    (hg : ∀ (ω : ι → σ) (a : σ), g (update ω i0 a) = g ω) :
    ∑ ω : ι → σ, centerZ f (ω i0) * g ω = 0 := by
  classical
  let e : (ι → σ) ≃ σ × ({j // j ≠ i0} → σ) := Equiv.funSplitAt i0 σ
  rw [show ∑ ω : ι → σ, centerZ f (ω i0) * g ω =
        ∑ p : σ × ({j // j ≠ i0} → σ), centerZ f p.1 * g (e.symm p) from by
    refine (Fintype.sum_equiv e.symm
      (fun p => centerZ f p.1 * g (e.symm p))
      (fun ω => centerZ f (ω i0) * g ω) ?_).symm
    intro p
    have : e.symm p i0 = p.1 := by
      rcases p with ⟨a, τ⟩
      simp [e, Equiv.funSplitAt_symm_apply]
    simp [this]]
  rw [Fintype.sum_prod_type]
  let a0 : σ := Classical.arbitrary σ
  have hg' : ∀ (a : σ) (τ : {j // j ≠ i0} → σ),
      g (e.symm (a, τ)) = g (e.symm (a0, τ)) := by
    intro a τ
    have hupd : e.symm (a, τ) = update (e.symm (a0, τ)) i0 a := by
      ext j
      by_cases hj : j = i0
      · subst hj; simp [e, Equiv.funSplitAt_symm_apply]
      · simp [e, Equiv.funSplitAt_symm_apply, hj, update_of_ne]
    rw [hupd, hg]
  calc ∑ a : σ, ∑ τ : {j // j ≠ i0} → σ, centerZ f a * g (e.symm (a, τ))
      = ∑ a : σ, ∑ τ : {j // j ≠ i0} → σ, centerZ f a * g (e.symm (a0, τ)) := by
        refine sum_congr rfl fun a _ => sum_congr rfl fun τ _ => by rw [hg']
    _ = ∑ τ : {j // j ≠ i0} → σ, ∑ a : σ, centerZ f a * g (e.symm (a0, τ)) := by
        rw [sum_comm]
    _ = ∑ τ : {j // j ≠ i0} → σ, g (e.symm (a0, τ)) * ∑ a : σ, centerZ f a := by
        refine sum_congr rfl fun τ _ => ?_
        set c := g (e.symm (a0, τ))
        calc ∑ a : σ, centerZ f a * c
            = ∑ a : σ, c * centerZ f a := by refine sum_congr rfl fun _ _ => mul_comm _ _
          _ = c * ∑ a : σ, centerZ f a := (mul_sum _ _ _).symm
    _ = ∑ τ : {j // j ≠ i0} → σ, g (e.symm (a0, τ)) * 0 := by simp [centerZ_mean]
    _ = 0 := by simp

lemma avg_prod_singleton {σ : Type*} [Fintype σ] [Nonempty σ]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : σ → Bool) {d : ℕ} (u : Fin d → ι) (k : Fin d)
    (honce : ∀ k' : Fin d, u k' = u k → k' = k) :
    ∑ ω : ι → σ, ∏ i : Fin d, centerZ f (ω (u i)) = 0 := by
  classical
  let i0 := u k
  let g : (ι → σ) → ℚ := fun ω =>
    ∏ i ∈ (univ.erase k), centerZ f (ω (u i))
  have hprod' : ∀ ω, (∏ i : Fin d, centerZ f (ω (u i))) = centerZ f (ω i0) * g ω := by
    intro ω
    have huniv : (univ : Finset (Fin d)) = insert k (univ.erase k) :=
      (insert_erase (mem_univ k)).symm
    rw [show (∏ i : Fin d, centerZ f (ω (u i))) =
          ∏ i ∈ (univ : Finset (Fin d)), centerZ f (ω (u i)) from rfl, huniv,
      prod_insert (notMem_erase _ _)]
  simp_rw [hprod']
  refine sum_update_center f i0 g ?_
  intro ω a
  apply prod_congr rfl
  intro i hi
  have hike : i ≠ k := (mem_erase.mp hi).1
  have hui : u i ≠ i0 := fun h => hike (honce i h)
  rw [update_of_ne hui]

lemma image_card_le_of_min_mult_two {ι : Type*} [DecidableEq ι] {s : ℕ}
    (u : Fin (2 * s) → ι)
    (h : ∀ y ∈ (univ : Finset (Fin (2 * s))).image u,
        2 ≤ #{k : Fin (2 * s) | u k = y}) :
    #((univ : Finset (Fin (2 * s))).image u) ≤ s := by
  classical
  have hsum : ∑ y ∈ univ.image u, #{k : Fin (2 * s) | u k = y} = 2 * s := by
    calc ∑ y ∈ univ.image u, #{k | u k = y}
        = ∑ y ∈ univ.image u, ∑ k : Fin (2 * s), if u k = y then (1 : ℕ) else 0 := by
            refine sum_congr rfl fun y _ => by simp [sum_boole]
      _ = ∑ k : Fin (2 * s), ∑ y ∈ univ.image u, if u k = y then (1 : ℕ) else 0 := by
            rw [sum_comm]
      _ = ∑ k : Fin (2 * s), (1 : ℕ) := by
            refine sum_congr rfl fun k _ => ?_
            have hy : u k ∈ univ.image u := mem_image_of_mem _ (mem_univ _)
            rw [sum_eq_single (u k)]
            · simp
            · intro y _ hyne; simp [Ne.symm hyne]
            · exact fun hh => (hh hy).elim
      _ = 2 * s := by simp [card_univ]
  have hge : ∑ y ∈ univ.image u, (2 : ℕ) ≤ ∑ y ∈ univ.image u, #{k | u k = y} :=
    sum_le_sum fun y hy => h y hy
  have : 2 * #(univ.image u) ≤ 2 * s := by
    simpa [mul_comm, sum_const, nsmul_eq_mul, hsum] using hge
  exact Nat.le_of_mul_le_mul_left this (by decide : 0 < 2)

lemma exists_unique_preimage_of_image_gt {ι : Type*} [DecidableEq ι] {s : ℕ}
    (u : Fin (2 * s) → ι) (h : s < #((univ : Finset (Fin (2 * s))).image u)) :
    ∃ k : Fin (2 * s), ∀ k' : Fin (2 * s), u k' = u k → k' = k := by
  classical
  by_contra hne
  push Not at hne
  have hge : ∀ y ∈ univ.image u, 2 ≤ #{k : Fin (2 * s) | u k = y} := by
    intro y hy
    obtain ⟨k, _, rfl⟩ := mem_image.mp hy
    obtain ⟨k', heq, hne'⟩ := hne k
    exact one_lt_card.2 ⟨k, by simp, k', by simp [heq], Ne.symm hne'⟩
  exact (not_lt_of_ge (image_card_le_of_min_mult_two u hge)) h

lemma abs_prod_center_le_one {σ : Type*} [Fintype σ] [Nonempty σ] {ι : Type*}
    (f : σ → Bool) {d : ℕ} (u : Fin d → ι) (ω : ι → σ) :
    |∏ i : Fin d, centerZ f (ω (u i))| ≤ 1 := by
  rw [abs_prod]
  calc ∏ i : Fin d, |centerZ f (ω (u i))|
      ≤ ∏ i : Fin d, (1 : ℚ) :=
        prod_le_prod (fun _ _ => abs_nonneg _) fun i _ => centerZ_abs_le_one f _
    _ = 1 := by simp

lemma sum_prod_center_of_image_gt {σ : Type*} [Fintype σ] [Nonempty σ]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : σ → Bool) {s : ℕ} (u : Fin (2 * s) → ι)
    (h : s < #((univ : Finset (Fin (2 * s))).image u)) :
    ∑ ω : ι → σ, ∏ i : Fin (2 * s), centerZ f (ω (u i)) = 0 := by
  obtain ⟨k, hk⟩ := exists_unique_preimage_of_image_gt u h
  exact avg_prod_singleton f u k hk

/-- Card of few-image maps Fin(2s)→ι, via equiv to Fin. -/
lemma card_few_image_general {ι : Type*} [Fintype ι] [DecidableEq ι] (s : ℕ) (hs : 1 ≤ s) :
    #{u : Fin (2 * s) → ι | #((univ : Finset (Fin (2 * s))).image u) ≤ s} ≤
      s ^ (2 * s + 1) * (Fintype.card ι) ^ s := by
  classical
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let Φ : (Fin (2 * s) → ι) ≃ (Fin (2 * s) → Fin (Fintype.card ι)) :=
    Equiv.piCongrRight fun _ => e
  have hEq :
      #{u : Fin (2 * s) → ι | #(univ.image u) ≤ s} =
        #{v : Fin (2 * s) → Fin (Fintype.card ι) | #(univ.image v) ≤ s} := by
    refine card_equiv Φ fun u => ?_
    simp only [mem_filter, mem_univ, true_and]
    change #(univ.image u) ≤ s ↔ #(univ.image (Φ u)) ≤ s
    have him : univ.image (Φ u) = (univ.image u).map e.toEmbedding := by
      ext x
      constructor
      · intro hx
        rcases mem_image.mp hx with ⟨i, _, hi⟩
        refine mem_map.2 ⟨u i, mem_image_of_mem u (mem_univ i), ?_⟩
        simp [Φ] at hi ⊢; exact hi
      · intro hx
        rcases mem_map.mp hx with ⟨y, hy, rfl⟩
        rcases mem_image.mp hy with ⟨i, _, rfl⟩
        refine mem_image.2 ⟨i, mem_univ i, ?_⟩
        simp [Φ]
    rw [him, card_map]
  rw [hEq]
  simpa using card_few_distinct_moment (Fintype.card ι) s hs

/-- Centered even moment: ∑_ω (∑_i Z_i)^{2s} ≤ (#ι)^s · s^{2s+1} · (#σ)^{#ι}. -/
lemma centered_moment_bound {σ : Type*} [Fintype σ] [Nonempty σ]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : σ → Bool) (s : ℕ) (hs : 1 ≤ s) :
    ∑ ω : ι → σ, (∑ i : ι, centerZ f (ω i)) ^ (2 * s) ≤
      ((Fintype.card ι : ℚ) ^ s * (s : ℚ) ^ (2 * s + 1) *
        (Fintype.card σ : ℚ) ^ Fintype.card ι) := by
  classical
  -- Expand
  have hexpand : ∀ (ω : ι → σ),
      (∑ i : ι, centerZ f (ω i)) ^ (2 * s) =
        ∑ u : Fin (2 * s) → ι, ∏ j : Fin (2 * s), centerZ f (ω (u j)) := by
    intro ω
    exact Fintype.sum_pow (fun i : ι => centerZ f (ω i)) (2 * s)
  have hswap :
      ∑ ω : ι → σ, (∑ i : ι, centerZ f (ω i)) ^ (2 * s) =
        ∑ u : Fin (2 * s) → ι,
          ∑ ω : ι → σ, ∏ j : Fin (2 * s), centerZ f (ω (u j)) := by
    simp_rw [hexpand]
    exact sum_comm
  -- Split
  let few : Finset (Fin (2 * s) → ι) :=
    univ.filter (fun u => #(univ.image u) ≤ s)
  let many : Finset (Fin (2 * s) → ι) :=
    univ.filter (fun u => s < #(univ.image u))
  have hpart : (univ : Finset (Fin (2 * s) → ι)) = few ∪ many := by
    ext u; simp [few, many]; omega
  have hdisj : Disjoint few many := by
    refine disjoint_filter.2 fun u _ h1 h2 => (not_lt_of_ge h1) h2
  -- Many vanish
  have hmany0 :
      ∑ u ∈ many, ∑ ω : ι → σ, ∏ j : Fin (2 * s), centerZ f (ω (u j)) = 0 := by
    apply sum_eq_zero
    intro u hu
    simp only [many, mem_filter, mem_univ, true_and] at hu
    exact sum_prod_center_of_image_gt f u hu
  -- Rewrite LHS as few-sum
  have hLHS :
      ∑ ω : ι → σ, (∑ i : ι, centerZ f (ω i)) ^ (2 * s) =
        ∑ u ∈ few, ∑ ω : ι → σ, ∏ j : Fin (2 * s), centerZ f (ω (u j)) := by
    rw [hswap]
    have hrew : ∑ u : Fin (2 * s) → ι, ∑ ω : ι → σ, ∏ j : Fin (2 * s), centerZ f (ω (u j)) =
        ∑ u ∈ few ∪ many, ∑ ω : ι → σ, ∏ j : Fin (2 * s), centerZ f (ω (u j)) := by
      rw [← hpart]
    rw [hrew, sum_union hdisj, hmany0, add_zero]
  -- Bound each |∑_ω prod| ≤ (#σ)^{#ι}
  have hcard_fun : (Fintype.card (ι → σ) : ℚ) = (Fintype.card σ : ℚ) ^ Fintype.card ι := by
    simp [Fintype.card_fun]
  have hterm : ∀ u : Fin (2 * s) → ι,
      |∑ ω : ι → σ, ∏ j : Fin (2 * s), centerZ f (ω (u j))| ≤
        (Fintype.card σ : ℚ) ^ Fintype.card ι := by
    intro u
    have h1 : |∑ ω : ι → σ, ∏ j : Fin (2 * s), centerZ f (ω (u j))| ≤
        ∑ ω : ι → σ, |∏ j : Fin (2 * s), centerZ f (ω (u j))| :=
      abs_sum_le_sum_abs _ _
    have h2 : ∑ ω : ι → σ, |∏ j : Fin (2 * s), centerZ f (ω (u j))| ≤
        ∑ ω : ι → σ, (1 : ℚ) :=
      sum_le_sum fun ω _ => abs_prod_center_le_one f u ω
    have h3 : ∑ ω : ι → σ, (1 : ℚ) = (Fintype.card (ι → σ) : ℚ) := by
      simp [sum_const, nsmul_eq_mul, card_univ]
    exact h1.trans (h2.trans (le_of_eq (h3.trans hcard_fun)))
  have hfew_abs :
      |∑ u ∈ few, ∑ ω : ι → σ, ∏ j : Fin (2 * s), centerZ f (ω (u j))| ≤
        (#few : ℚ) * (Fintype.card σ : ℚ) ^ Fintype.card ι := by
    have h1 : |∑ u ∈ few, ∑ ω : ι → σ, ∏ j : Fin (2 * s), centerZ f (ω (u j))| ≤
        ∑ u ∈ few, |∑ ω : ι → σ, ∏ j : Fin (2 * s), centerZ f (ω (u j))| :=
      abs_sum_le_sum_abs _ _
    have h2 : ∑ u ∈ few, |∑ ω : ι → σ, ∏ j : Fin (2 * s), centerZ f (ω (u j))| ≤
        ∑ u ∈ few, (Fintype.card σ : ℚ) ^ Fintype.card ι :=
      sum_le_sum fun u _ => hterm u
    have h3 : ∑ u ∈ few, (Fintype.card σ : ℚ) ^ Fintype.card ι =
        (#few : ℚ) * (Fintype.card σ : ℚ) ^ Fintype.card ι := by
      simp [sum_const, nsmul_eq_mul]
    exact h1.trans (h2.trans h3.le)
  -- LHS ≥ 0 because it is a sum of even powers
  have hnn :
      0 ≤ ∑ ω : ι → σ, (∑ i : ι, centerZ f (ω i)) ^ (2 * s) := by
    refine sum_nonneg fun ω _ => ?_
    exact Even.pow_nonneg (even_two_mul s) _
  -- So few-sum = LHS ≥ 0, hence ≤ |few-sum|
  have hpos_few :
      0 ≤ ∑ u ∈ few, ∑ ω : ι → σ, ∏ j : Fin (2 * s), centerZ f (ω (u j)) := by
    rwa [← hLHS]
  have hle :
      ∑ u ∈ few, ∑ ω : ι → σ, ∏ j : Fin (2 * s), centerZ f (ω (u j)) ≤
        (#few : ℚ) * (Fintype.card σ : ℚ) ^ Fintype.card ι :=
    (le_abs_self _).trans hfew_abs
  -- #few bound
  have hfew_card : (#few : ℕ) ≤ s ^ (2 * s + 1) * (Fintype.card ι) ^ s := by
    simpa [few] using card_few_image_general (ι := ι) s hs
  rw [hLHS]
  refine hle.trans ?_
  have hcast : (#few : ℚ) ≤ (s : ℚ) ^ (2 * s + 1) * (Fintype.card ι : ℚ) ^ s := by
    exact_mod_cast hfew_card
  calc (#few : ℚ) * (Fintype.card σ : ℚ) ^ Fintype.card ι
      ≤ ((s : ℚ) ^ (2 * s + 1) * (Fintype.card ι : ℚ) ^ s) *
          (Fintype.card σ : ℚ) ^ Fintype.card ι :=
        mul_le_mul_of_nonneg_right hcast (by positivity)
    _ = (Fintype.card ι : ℚ) ^ s * (s : ℚ) ^ (2 * s + 1) *
          (Fintype.card σ : ℚ) ^ Fintype.card ι := by ring


/-! ## Sol (5) Markov form (Nat-facing, avoids heavy ℚ field simp) -/

noncomputable def indB {σ : Type*} (f : σ → Bool) (x : σ) : ℚ :=
  if f x then (1 : ℚ) else 0

noncomputable def meanB {σ : Type*} [Fintype σ] (f : σ → Bool) : ℚ :=
  ((#{y : σ | f y = true}) : ℚ) / (Fintype.card σ : ℚ)

lemma indB_eq_center_add_mean {σ : Type*} [Fintype σ] (f : σ → Bool) (x : σ) :
    indB f x = centerZ f x + meanB f := by
  simp only [indB, centerZ, meanB]; ring

lemma sum_indB {σ : Type*} [Fintype σ] {ι : Type*} [Fintype ι]
    (f : σ → Bool) (ω : ι → σ) :
    ∑ i : ι, indB f (ω i) =
      ∑ i : ι, centerZ f (ω i) + (Fintype.card ι : ℚ) * meanB f := by
  have hterm : ∀ i, indB f (ω i) = centerZ f (ω i) + meanB f := fun i =>
    indB_eq_center_add_mean f (ω i)
  simp_rw [hterm, sum_add_distrib]
  simp [sum_const, nsmul_eq_mul, card_univ]

/-- Centered moment in the exact shape needed by Markov: bound ≤ s^{2s+1} n^s N. -/
lemma centered_moment_bound' {σ : Type*} [Fintype σ] [Nonempty σ]
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (f : σ → Bool) (s : ℕ) (hs : 1 ≤ s) :
    ∑ ω : ι → σ, (∑ i : ι, centerZ f (ω i)) ^ (2 * s) ≤
      ((Fintype.card ι : ℚ) ^ s * (s : ℚ) ^ (2 * s + 1) *
        (Fintype.card σ : ℚ) ^ Fintype.card ι) :=
  centered_moment_bound (ι := ι) f s hs

/-- Sol (5): fraction of configurations with ∑ indB > β |ι| is
≤ s^{2s+1} / (ε^{2s} |ι|^s), when mean ≤ β − ε. -/
theorem moment_bound_zero_one {σ : Type*} [Fintype σ] [Nonempty σ]
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (f : σ → Bool) (s : ℕ) (hs : 1 ≤ s)
    (β ε : ℚ) (hε : 0 < ε)
    (hmean : meanB f ≤ β - ε) :
    (#{ω : ι → σ | β * (Fintype.card ι : ℚ) < ∑ i : ι, indB f (ω i)} : ℚ) *
        (ε * (Fintype.card ι : ℚ)) ^ (2 * s) ≤
      (Fintype.card ι : ℚ) ^ s * (s : ℚ) ^ (2 * s + 1) *
        (Fintype.card σ : ℚ) ^ Fintype.card ι := by
  classical
  set nι : ℚ := (Fintype.card ι : ℚ)
  have hnι : (0 : ℚ) < nι := Nat.cast_pos.mpr Fintype.card_pos
  let bad : Finset (ι → σ) :=
    univ.filter (fun ω => β * nι < ∑ i : ι, indB f (ω i))
  have hbad_center : ∀ ω ∈ bad,
      ε * nι < ∑ i : ι, centerZ f (ω i) := by
    intro ω hω
    simp only [bad, mem_filter, mem_univ, true_and] at hω
    have hsum := sum_indB (ι := ι) f ω
    have hle : ∑ i, indB f (ω i) ≤ ∑ i, centerZ f (ω i) + nι * (β - ε) := by
      rw [hsum]
      have : nι * meanB f ≤ nι * (β - ε) :=
        mul_le_mul_of_nonneg_left hmean (le_of_lt hnι)
      simpa [nι] using add_le_add_left this (∑ i, centerZ f (ω i))
    have hεeq : β * nι - nι * (β - ε) = ε * nι := by ring
    have hlt : β * nι - nι * (β - ε) < ∑ i, centerZ f (ω i) := by
      have h := lt_of_lt_of_le hω hle
      linarith
    rwa [hεeq] at hlt
  have hεn : 0 ≤ ε * nι := mul_nonneg (le_of_lt hε) (le_of_lt hnι)
  have h2 : ∑ ω ∈ bad, (ε * nι) ^ (2 * s) ≤
      ∑ ω ∈ bad, (∑ i : ι, centerZ f (ω i)) ^ (2 * s) := by
    refine sum_le_sum fun ω hω => ?_
    have hc := hbad_center ω hω
    exact pow_le_pow_left₀ hεn (le_of_lt hc) _
  have h3 : ∑ ω ∈ bad, (ε * nι) ^ (2 * s) = (#bad : ℚ) * (ε * nι) ^ (2 * s) := by
    simp [sum_const, nsmul_eq_mul]
  have h1 : ∑ ω ∈ bad, (∑ i : ι, centerZ f (ω i)) ^ (2 * s) ≤
      ∑ ω : ι → σ, (∑ i : ι, centerZ f (ω i)) ^ (2 * s) :=
    sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ =>
      Even.pow_nonneg (even_two_mul s) _
  have hmarkov : (#bad : ℚ) * (ε * nι) ^ (2 * s) ≤
      ∑ ω : ι → σ, (∑ i : ι, centerZ f (ω i)) ^ (2 * s) := by
    calc (#bad : ℚ) * (ε * nι) ^ (2 * s)
        = ∑ ω ∈ bad, (ε * nι) ^ (2 * s) := h3.symm
      _ ≤ ∑ ω ∈ bad, (∑ i, centerZ f (ω i)) ^ (2 * s) := h2
      _ ≤ _ := h1
  have hmom := centered_moment_bound' (ι := ι) f s hs
  have hcomb := hmarkov.trans hmom
  -- Identify bad with the filter in the statement
  have hbad_eq : (#bad : ℚ) =
      (#{ω : ι → σ | β * (Fintype.card ι : ℚ) < ∑ i : ι, indB f (ω i)} : ℚ) := by
    simp only [bad, nι]
  rw [← hbad_eq]
  simpa [nι] using hcomb

/-! ### from Maps.lean -/

/-!
# Maps from capacity labellings (Sol conversion step)
-/




lemma card_bool_powerset (B : Type*) [Fintype B] [DecidableEq B] :
    Fintype.card (Bool × Finset B) = 2 ^ (Fintype.card B + 1) := by
  rw [Fintype.card_prod, Fintype.card_finset, Fintype.card_bool, pow_succ, mul_comm]

lemma powerset_slot_card {U : Type*} [DecidableEq U]
    {t k : ℕ} (ht : 1 ≤ t) (hk : t ≤ k) (B : Finset U) (hB : #B = k - t) :
    Fintype.card (Bool × Finset B) = 2 ^ k / 2 ^ (t - 1) := by
  rw [card_bool_powerset, Fintype.card_coe, hB]
  have hsum : k - t + 1 + (t - 1) = k := by omega
  have hmul : 2 ^ (k - t + 1) * 2 ^ (t - 1) = 2 ^ k := by rw [← pow_add, hsum]
  exact (Nat.div_eq_of_eq_mul_left (Nat.two_pow_pos _) hmul.symm).symm

def liftSet {U : Type*} [DecidableEq U] (B : Finset U)
    (C : Finset B) (T : Finset {x // x ∉ B}) : Finset U :=
  C.image Subtype.val ∪ T.image Subtype.val

lemma recover_C {U : Type*} [DecidableEq U] (B : Finset U)
    (C : Finset B) (T : Finset {x // x ∉ B}) :
    (univ : Finset B).filter (fun (b : B) => (b : U) ∈ liftSet B C T) = C := by
  apply subset_antisymm
  · intro (b : B) hb
    have hW : (b : U) ∈ liftSet B C T := (mem_filter.mp hb).2
    rcases mem_union.mp hW with hC | hT
    · obtain ⟨b', hbC, heq⟩ := mem_image.mp hC
      exact Subtype.val_injective heq ▸ hbC
    · obtain ⟨v, _, heq⟩ := mem_image.mp hT
      exact absurd (heq ▸ b.property : (v : U) ∈ B) v.property
  · intro (b : B) hbC
    exact mem_filter.mpr ⟨mem_univ _, mem_union.mpr (Or.inl (mem_image_of_mem _ hbC))⟩

lemma recover_T {U : Type*} [DecidableEq U] [Fintype U] (B : Finset U)
    (C : Finset B) (T : Finset {x // x ∉ B}) :
    (univ : Finset {x // x ∉ B}).filter
      (fun (x : {x // x ∉ B}) => (x : U) ∈ liftSet B C T) = T := by
  apply subset_antisymm
  · intro x hx
    have hW : (x : U) ∈ liftSet B C T := (mem_filter.mp hx).2
    rcases mem_union.mp hW with hC | hT
    · obtain ⟨b, _, heq⟩ := mem_image.mp hC
      exact absurd (heq ▸ b.property : (x : U) ∈ B) x.property
    · obtain ⟨x', hxT, heq⟩ := mem_image.mp hT
      exact Subtype.val_injective heq ▸ hxT
  · intro x hxT
    exact mem_filter.mpr ⟨mem_univ _, mem_union.mpr (Or.inr (mem_image_of_mem _ hxT))⟩

lemma lift_subset {U : Type*} [DecidableEq U] {B Y : Finset U}
    (hBY : B ⊆ Y) (C : Finset B) {T : Finset {x // x ∉ B}}
    (hT : ∀ x ∈ T, (x : U) ∈ Y) :
    liftSet B C T ⊆ Y := by
  intro x hx
  rcases mem_union.mp hx with hC | hT'
  · obtain ⟨b, _, rfl⟩ := mem_image.mp hC
    exact hBY b.property
  · obtain ⟨v, hv, rfl⟩ := mem_image.mp hT'
    exact hT v hv

/-- Decode the `B`-part of a set. -/
def decodeC {U : Type*} [DecidableEq U] (B : Finset U) (W : Finset U) : Finset B :=
  (univ : Finset B).filter (fun (b : B) => (b : U) ∈ W)

/-- Decode the `V`-part of a set. -/
def decodeT {U : Type*} [DecidableEq U] [Fintype U] (B : Finset U) (W : Finset U) :
    Finset {x // x ∉ B} :=
  (univ : Finset {x // x ∉ B}).filter (fun (x : {x // x ∉ B}) => (x : U) ∈ W)

lemma decodeC_lift {U : Type*} [DecidableEq U] (B : Finset U)
    (C : Finset B) (T : Finset {x // x ∉ B}) :
    decodeC B (liftSet B C T) = C := recover_C B C T

lemma decodeT_lift {U : Type*} [DecidableEq U] [Fintype U] (B : Finset U)
    (C : Finset B) (T : Finset {x // x ∉ B}) :
    decodeT B (liftSet B C T) = T := recover_T B C T

/-- Lookup colour at a slot via an embedding of a colour-set. -/
noncomputable def lookupColour {U : Type*} [DecidableEq U] {B : Finset U}
    {S : Finset U} (η : S ↪ Bool × Finset B) (uStar : U)
    (slot : Bool × Finset B) : U :=
  if h : ∃ u : S, η u = slot then (Classical.choose h : S).1 else uStar

lemma lookupColour_eq {U : Type*} [DecidableEq U] {B : Finset U}
    {S : Finset U} (η : S ↪ Bool × Finset B) (uStar : U)
    (u : S) :
    lookupColour η uStar (η u) = u.1 := by
  have hex : ∃ u' : S, η u' = η u := ⟨u, rfl⟩
  have hch : Classical.choose hex = u := η.injective (Classical.choose_spec hex)
  simp only [lookupColour, dif_pos hex, hch]

/-- Core combinatorial conversion from capacity labellings to covering maps. -/
theorem maps_from_capacity
    {U : Type*} [Fintype U] [DecidableEq U] [Nonempty U]
    {t k : ℕ} (_ht : 2 ≤ t) (hk : t ≤ k)
    (hU : Fintype.card U = 2 ^ k)
    (B : Finset U) (hB : #B = k - t)
    (v : U → {x // x ∉ B} → E t)
    (hcap : ∀ T : Finset {x // x ∉ B}, T.Nonempty → #T ≤ t →
        #{u : U | IsCircuit (v u) T} ≤ 2 ^ k / q t)
    (hcover : ∀ Z : Finset {x // x ∉ B}, #Z = t →
        ∀ u : U, ∃ T ⊆ Z, IsCircuit (v u) T) :
    ∃ (g0 g1 : Finset U → U),
      ∀ Y : Finset U, #Y = k → B ⊆ Y →
        (Y.powerset.image g0 ∪ Y.powerset.image g1) = (univ : Finset U) := by
  classical
  let V := {x : U // x ∉ B}
  let Omega := Bool × Finset B
  have hOm : Fintype.card Omega = 2 ^ k / q t := by
    simpa [Omega, q] using powerset_slot_card (U := U) (by omega : 1 ≤ t) hk B hB
  let L : Finset V → Finset U := fun T =>
    univ.filter (fun u => IsCircuit (v u) T)
  have hLle : ∀ T : Finset V, T.Nonempty → #T ≤ t → #(L T) ≤ Fintype.card Omega := by
    intro T hne hc
    simpa [L, hOm] using hcap T hne hc
  let Good := {T : Finset V // T.Nonempty ∧ #T ≤ t}
  let η : (g : Good) → L g.1 ↪ Omega := fun g =>
    (Function.Embedding.nonempty_of_card_le (by
      simpa [Fintype.card_coe] using hLle g.1 g.2.1 g.2.2)).some
  let uStar : U := Classical.arbitrary U
  -- g_i(W) looks up via decode
  let gBool : Bool → Finset U → U := fun i W =>
    let T0 := decodeT B W
    let C0 := decodeC B W
    if hg : T0.Nonempty ∧ #T0 ≤ t then
      lookupColour (η ⟨T0, hg⟩) uStar (i, C0)
    else uStar
  refine ⟨gBool false, gBool true, ?_⟩
  intro Y hYcard hBY
  refine eq_univ_iff_forall.2 fun u => ?_
  let Z : Finset V := decodeT B Y
  have hZcard : #Z = t := by
    have hdisj : Disjoint B (Z.image Subtype.val) := by
      refine disjoint_left.2 fun x hxB hxZ => ?_
      obtain ⟨⟨_, hxB'⟩, _, rfl⟩ := mem_image.mp hxZ
      exact hxB' hxB
    have hunion : B ∪ Z.image Subtype.val = Y := by
      ext x
      constructor
      · intro hx
        rcases mem_union.mp hx with hB | hZ
        · exact hBY hB
        · obtain ⟨v, hvZ, rfl⟩ := mem_image.mp hZ
          exact (mem_filter.mp hvZ).2
      · intro hxY
        by_cases hxB : x ∈ B
        · exact mem_union.mpr (Or.inl hxB)
        · refine mem_union.mpr (Or.inr (mem_image.mpr ?_))
          exact ⟨⟨x, hxB⟩, mem_filter.mpr ⟨mem_univ _, hxY⟩, rfl⟩
    have hcard : #Y = #B + #Z := by
      rw [← hunion, card_union_of_disjoint hdisj,
        card_image_of_injective _ Subtype.val_injective]
    omega
  obtain ⟨T, hTZ, hCirc⟩ := hcover Z hZcard u
  have hTne : T.Nonempty := hCirc.1
  have hTcard : #T ≤ t := (card_le_card hTZ).trans hZcard.le
  have huL : u ∈ L T := by simpa [L] using hCirc
  let gT : Good := ⟨T, ⟨hTne, hTcard⟩⟩
  let e : Omega := η gT ⟨u, huL⟩
  let i : Bool := e.1
  let C : Finset B := e.2
  have hη : η gT ⟨u, huL⟩ = (i, C) := Prod.ext rfl rfl
  let W := liftSet B C T
  have hWsub : W ⊆ Y :=
    lift_subset hBY C fun x hxT => (mem_filter.mp (hTZ hxT)).2
  have hWY : W ∈ Y.powerset := mem_powerset.mpr hWsub
  have hDecT : decodeT B W = T := decodeT_lift B C T
  have hDecC : decodeC B W = C := decodeC_lift B C T
  have hlookup : lookupColour (η gT) uStar (i, C) = u := by
    have := lookupColour_eq (η gT) uStar ⟨u, huL⟩
    simpa [hη] using this
  have hslot : gBool i W = u := by
    dsimp [gBool]
    rw [hDecT, hDecC, dif_pos ⟨hTne, hTcard⟩]
    -- η ⟨T, _⟩ vs η gT
    have hηeq : η ⟨T, ⟨hTne, hTcard⟩⟩ = η gT := rfl
    rw [hηeq]
    exact hlookup
  cases hi : i with
  | false =>
    have hslot' : gBool false W = u := by simpa [hi] using hslot
    exact mem_union.2 (Or.inl (mem_image.2 ⟨W, hWY, hslot'⟩))
  | true =>
    have hslot' : gBool true W = u := by simpa [hi] using hslot
    exact mem_union.2 (Or.inr (mem_image.2 ⟨W, hWY, hslot'⟩))

/-! ### from GrowingCore.lean -/

/-!
# Growing-core / prescribed-star integral obstruction (Sol Round 8 / A5)

Honesty: does **not** settle PAIR or Erdős #624 — only a prescribed-star covering
obstruction on cores sharing a fixed (k−t)-set B.

Credit: derived from GPT 6.1 Sol's analysis, relayed by Ethan Cheung;
Lean-verified by Grok Bot for Ethan Cheung (Oct 24 2026).

Corrected: `A_t = [t(t+1)]^{2t+3} · 2^{4t(t+1)}`.
-/



set_option autoImplicit false

abbrev Atom (t : ℕ) : Type := Σ z : E t, Fin (weight t z)
def decode {t : ℕ} (a : Atom t) : E t := a.1

instance (t : ℕ) : Fintype (Atom t) := Sigma.instFintype
instance (t : ℕ) : DecidableEq (Atom t) := Sigma.instDecidableEqSigma

lemma card_Atom (t : ℕ) (ht : 2 ≤ t) : Fintype.card (Atom t) = D t := by
  classical
  calc Fintype.card (Atom t)
      = ∑ z : E t, Fintype.card (Fin (weight t z)) := by rw [Fintype.card_sigma]
    _ = ∑ z : E t, weight t z := by simp [Fintype.card_fin]
    _ = D t := sum_weight t ht

lemma D_pos (t : ℕ) (ht : 2 ≤ t) : 0 < D t := by
  have hq := q_ge_two ht
  unfold D
  have h1 : 0 < 4 * t := by omega
  have h2 : 0 < q t := by omega
  have h3 : 0 < (q t) ^ 2 := pow_pos h2 2
  have h4 : 0 < q t - 1 := by omega
  exact Nat.mul_pos (Nat.mul_pos h1 h3) h4

lemma Atom_nonempty (t : ℕ) (ht : 2 ≤ t) : Nonempty (Atom t) :=
  Fintype.card_pos_iff.mp (by rw [card_Atom t ht]; exact D_pos t ht)

lemma card_atom_circuits (t j : ℕ) (_ht : 2 ≤ t) :
    #{ψ : Fin j → Atom t | IsCircuitTuple (t := t) (decode ∘ ψ)} = circuitWeight t j := by
  classical
  let P : (Fin j → E t) → Prop := IsCircuitTuple (t := t)
  let e : (Fin j → Atom t) ≃ (Σ φ : Fin j → E t, ∀ i, Fin (weight t (φ i))) :=
    { toFun := fun ψ => ⟨fun i => decode (ψ i), fun i => (ψ i).2⟩
      invFun := fun ⟨φ, w⟩ i => ⟨φ i, w i⟩
      left_inv := fun ψ => by funext i; exact Sigma.eta (ψ i)
      right_inv := fun _ => rfl }
  have hsum :
      ∑ ψ : Fin j → Atom t, (if P (decode ∘ ψ) then (1 : ℕ) else 0) =
        ∑ φ : Fin j → E t, (if P φ then ∏ i, weight t (φ i) else 0) := by
    have h := Fintype.sum_equiv e
      (fun ψ => if P (decode ∘ ψ) then (1 : ℕ) else 0)
      (fun p => if P p.1 then (1 : ℕ) else 0)
      (fun ψ => rfl)
    rw [h, Fintype.sum_sigma]
    refine Fintype.sum_congr _ _ fun φ => ?_
    split_ifs with hP
    · change ∑ _w : ∀ i, Fin (weight t (φ i)), (1 : ℕ) = ∏ i, weight t (φ i)
      rw [Finset.sum_const, card_univ, nsmul_eq_mul, mul_one]
      simp [Fintype.card_pi, Fintype.card_fin]
    · simp
  have hL : #{ψ : Fin j → Atom t | P (decode ∘ ψ)} =
      ∑ ψ : Fin j → Atom t, (if P (decode ∘ ψ) then (1 : ℕ) else 0) := by
    simp [sum_boole]
  have hR : ∑ φ : Fin j → E t, (if P φ then ∏ i, weight t (φ i) else 0) =
      circuitWeight t j := by
    simp only [circuitWeight, tupWeight, P, sum_filter]
  exact hL.trans (hsum.trans hR)

lemma q_le_εNat (t : ℕ) (ht : 2 ≤ t) : q t ≤ εNat t := by
  have hε := εNat_eq t (by omega)
  rw [hε]
  have : 1 ≤ 4 * t * q t := four_t_q_pos ht
  calc q t = 1 * q t := (one_mul _).symm
    _ ≤ (4 * t * q t) * q t := Nat.mul_le_mul_right _ this
    _ = 4 * t * q t ^ 2 := by ring

lemma circuit_mean_le {t j : ℕ} (ht : 2 ≤ t) (hj1 : 1 ≤ j) (hj : j ≤ t) :
    (circuitWeight t j : ℚ) / (D t : ℚ) ^ j ≤ (1 : ℚ) / q t - 1 / εNat t := by
  have hqpos : 0 < q t := lt_of_lt_of_le (by omega : 0 < 2) (q_ge_two ht)
  have hεpos : 0 < εNat t := εNat_pos (by omega)
  have hDpos := D_pos t ht
  have hεge := q_le_εNat t ht
  have hb := circuit_weight_bound ht hj1 hj
  have hcast : ((εNat t - q t : ℕ) : ℚ) = (εNat t : ℚ) - (q t : ℚ) :=
    Nat.cast_sub hεge
  have hbQ : (circuitWeight t j : ℚ) * q t * εNat t ≤
      (D t : ℚ) ^ j * ((εNat t : ℚ) - q t) := by
    calc (circuitWeight t j : ℚ) * q t * εNat t
        = ↑(circuitWeight t j * q t * εNat t) := by push_cast; ring
      _ ≤ ↑(D t ^ j * (εNat t - q t)) := Nat.cast_le.mpr hb
      _ = ↑(D t) ^ j * ↑(εNat t - q t) := by push_cast; ring
      _ = ↑(D t) ^ j * (↑(εNat t) - ↑(q t)) := by rw [hcast]
  have hden : (0 : ℚ) < (q t : ℚ) * εNat t :=
    mul_pos (Nat.cast_pos.mpr hqpos) (Nat.cast_pos.mpr hεpos)
  have hCW : (circuitWeight t j : ℚ) ≤
      (D t : ℚ) ^ j * (((εNat t : ℚ) - q t) / ((q t : ℚ) * εNat t)) := by
    have hmul : (circuitWeight t j : ℚ) * ((q t : ℚ) * εNat t) ≤
        (D t : ℚ) ^ j * ((εNat t : ℚ) - q t) := by
      convert hbQ using 1 <;> ring
    have key : (circuitWeight t j : ℚ) ≤
        ((D t : ℚ) ^ j * ((εNat t : ℚ) - q t)) / ((q t : ℚ) * εNat t) :=
      (le_div_iff₀ hden).2 hmul
    calc (circuitWeight t j : ℚ)
        ≤ ((D t : ℚ) ^ j * ((εNat t : ℚ) - q t)) / ((q t : ℚ) * εNat t) := key
      _ = (D t : ℚ) ^ j * (((εNat t : ℚ) - q t) / ((q t : ℚ) * εNat t)) := by ring
  have hid : ((εNat t : ℚ) - q t) / ((q t : ℚ) * εNat t) = (1 : ℚ) / q t - 1 / εNat t := by
    have hq0 : (q t : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hqpos)
    have hε0 : (εNat t : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hεpos)
    field_simp
  have hDne : (D t : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hDpos)
  have hpow : (D t : ℚ) ^ j ≠ 0 := pow_ne_zero _ hDne
  calc (circuitWeight t j : ℚ) / (D t : ℚ) ^ j
      ≤ ((D t : ℚ) ^ j * (((εNat t : ℚ) - q t) / ((q t : ℚ) * εNat t))) / (D t : ℚ) ^ j :=
        div_le_div_of_nonneg_right hCW (pow_nonneg (Nat.cast_nonneg _) _)
    _ = ((εNat t : ℚ) - q t) / ((q t : ℚ) * εNat t) := by field_simp [hpow]
    _ = (1 : ℚ) / q t - 1 / εNat t := hid

lemma sum_reindex {V : Type*} [DecidableEq V] {t : ℕ} {T : Finset V} {j : ℕ}
    (e : Fin j ≃ {x // x ∈ T}) (v : V → E t) :
    ∑ i : Fin j, v (e i) = ∑ x ∈ T, v x := by
  have h1 : ∑ i : Fin j, v (e i) = ∑ x : {x // x ∈ T}, v x :=
    Fintype.sum_equiv e (fun i => v (e i)) (fun x => v x) (fun _ => rfl)
  have h2 : ∑ x : {x // x ∈ T}, v x = ∑ x ∈ T, v x := by
    change ∑ x ∈ T.attach, v x = ∑ x ∈ T, v x
    exact sum_attach T v
  exact h1.trans h2

lemma isCircuit_to_tuple {V : Type*} [DecidableEq V] {t j : ℕ}
    {T : Finset V} (e : Fin j ≃ {x // x ∈ T}) (v : V → E t)
    (hj : 1 ≤ j) (hcard : #T = j) (hC : IsCircuit v T) :
    IsCircuitTuple (t := t) (fun i => v (e i)) := by
  classical
  obtain ⟨hne, hsum, hmin⟩ := hC
  refine ⟨hj, ?_, ?_⟩
  · exact (sum_reindex e v).trans hsum
  · intro S hSne hSneU h0
    let S' : Finset V := S.image fun i => (e i : V)
    have hinjOn : Set.InjOn (fun i : Fin j => (e i : V)) (S : Set _) := by
      intro i _ i' _ h; exact e.injective (Subtype.ext h)
    have hS'sub : S' ⊆ T := by
      intro x hx; obtain ⟨i, _, rfl⟩ := mem_image.mp hx; exact (e i).property
    have hS'ne : S'.Nonempty := hSne.image _
    have hS'neT : S' ≠ T := by
      intro hEq
      have hc : #S' = #T := congrArg card hEq
      have : #S = j := by rw [← card_image_of_injOn hinjOn, hc, hcard]
      have : S = univ :=
        eq_of_subset_of_card_le (subset_univ _)
          (by simpa [card_univ, Fintype.card_fin] using this.symm.le)
      exact hSneU this
    have hsumEq : ∑ x ∈ S', v x = ∑ i ∈ S, v (e i) := sum_image hinjOn
    exact hmin hS'sub hS'ne hS'neT (hsumEq.trans h0)

lemma sum_ind_factor {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (S : Finset α) (p : ({x // x ∈ S} → β) → Prop) [DecidablePred p] :
    ∑ f : α → β, (if p (fun x : {x // x ∈ S} => f x) then (1 : ℕ) else 0) =
      #{g : {x // x ∈ S} → β | p g} * (Fintype.card β) ^ (Fintype.card α - #S) := by
  classical
  let Ssub := {x // x ∈ S}
  let Fsub := {x // x ∉ S}
  let eV : α ≃ Ssub ⊕ Fsub :=
    { toFun := fun x => if hx : x ∈ S then Sum.inl ⟨x, hx⟩ else Sum.inr ⟨x, hx⟩
      invFun := fun y => match y with | .inl s => ↑s | .inr f => ↑f
      left_inv := fun x => by by_cases hx : x ∈ S <;> simp [hx]
      right_inv := fun y => by
        cases y with
        | inl s => simp [s.property]
        | inr f => simp [show ↑f ∉ S from f.property] }
  let eFun : (α → β) ≃ (Ssub → β) × (Fsub → β) :=
    (Equiv.arrowCongr eV (Equiv.refl β)).trans (Equiv.sumArrowEquivProdArrow Ssub Fsub β)
  have hrestrict (f : α → β) : (fun x : Ssub => f ↑x) = (eFun f).1 := by
    funext x
    show f ↑x = (Equiv.sumArrowEquivProdArrow Ssub Fsub β
      (Equiv.arrowCongr eV (Equiv.refl β) f)).1 x
    change f ↑x = ((f ∘ eV.symm) ∘ Sum.inl) x
    simp only [Function.comp_apply]
    simp [eV]
  have h1 : ∑ f : α → β, (if p (fun x : Ssub => f x) then (1 : ℕ) else 0) =
      ∑ g : (Ssub → β) × (Fsub → β), (if p g.1 then (1 : ℕ) else 0) :=
    Fintype.sum_equiv eFun _ _ fun f => by rw [hrestrict f]
  have hFcard : Fintype.card Fsub = Fintype.card α - #S := by
    have hS : Fintype.card Ssub = #S := Fintype.card_coe S
    have hsum : Fintype.card Ssub + Fintype.card Fsub = Fintype.card α := by
      rw [← Fintype.card_sum, Fintype.card_congr eV.symm]
    omega
  have h2 : ∑ g : (Ssub → β) × (Fsub → β), (if p g.1 then (1 : ℕ) else 0) =
      #{g : Ssub → β | p g} * Fintype.card (Fsub → β) := by
    rw [Fintype.sum_prod_type]
    have hstep : ∀ g1 : Ssub → β,
        (∑ _g2 : Fsub → β, (if p g1 then (1 : ℕ) else 0)) =
          (if p g1 then (1 : ℕ) else 0) * Fintype.card (Fsub → β) := by
      intro g1; simp [sum_const, card_univ]
    refine Eq.trans (Fintype.sum_congr _ _ hstep) ?_
    rw [← Finset.sum_mul]
    simp [sum_boole]
  have h3 : Fintype.card (Fsub → β) = Fintype.card β ^ (Fintype.card α - #S) := by
    rw [Fintype.card_fun, hFcard]
  exact h1.trans (h2.trans (by rw [h3]))

lemma card_small_subsets (V : Type*) [Fintype V] [DecidableEq V] (t : ℕ)
    (hn : 0 < Fintype.card V) :
    #{T : Finset V | T.Nonempty ∧ #T ≤ t} ≤ t * Fintype.card V ^ t := by
  classical
  let n := Fintype.card V
  have hle : ∀ j, j ≤ t → #(powersetCard j (univ : Finset V)) ≤ n ^ t := by
    intro j hjt
    calc #(powersetCard j univ) = n.choose j := by simp [card_powersetCard, card_univ, n]
      _ ≤ n ^ j := Nat.choose_le_pow n j
      _ ≤ n ^ t := Nat.pow_le_pow_right hn hjt
  have hsub : univ.filter (fun T : Finset V => T.Nonempty ∧ #T ≤ t) ⊆
      (Icc 1 t).biUnion fun j => powersetCard j univ := by
    intro T hT
    obtain ⟨hne, hc⟩ := (mem_filter.mp hT).2
    refine mem_biUnion.mpr ⟨#T, mem_Icc.mpr ⟨Nat.succ_le_of_lt (card_pos.mpr hne), hc⟩, ?_⟩
    exact mem_powersetCard.mpr ⟨subset_univ _, rfl⟩
  calc #{T : Finset V | T.Nonempty ∧ #T ≤ t}
      ≤ #((Icc 1 t).biUnion fun j => powersetCard j (univ : Finset V)) :=
        card_le_card hsub
    _ ≤ ∑ j ∈ Icc 1 t, #(powersetCard j (univ : Finset V)) := card_biUnion_le
    _ ≤ ∑ j ∈ Icc 1 t, n ^ t := sum_le_sum fun j hj => hle j (mem_Icc.mp hj).2
    _ = #(Icc 1 t) * n ^ t := by simp [sum_const, nsmul_eq_mul]
    _ ≤ t * n ^ t := Nat.mul_le_mul_right _ (by rw [Nat.card_Icc]; omega)

lemma meanB_circuit {V : Type*} [Fintype V] [DecidableEq V]
    {t : ℕ} (ht : 2 ≤ t) {T : Finset V} (hne : T.Nonempty) (hc : #T ≤ t) :
    meanB (fun ℓ : V → Atom t =>
      decide (IsCircuitTuple (t := t)
        (fun i : Fin #T => decode (ℓ (T.equivFin.symm i))))) ≤
      (1 : ℚ) / q t - 1 / εNat t := by
  classical
  set j := #T
  have hj1 : 1 ≤ j := Nat.succ_le_of_lt (card_pos.mpr hne)
  have hj : j ≤ t := hc
  let p : ({x // x ∈ T} → Atom t) → Prop := fun g =>
    IsCircuitTuple (t := t) (fun i : Fin j => decode (g (T.equivFin.symm i)))
  have hcount : #{ℓ : V → Atom t |
      IsCircuitTuple (t := t)
        (fun i : Fin j => decode (ℓ (T.equivFin.symm i)))} =
      circuitWeight t j * D t ^ (Fintype.card V - j) := by
    have hsum := sum_ind_factor (α := V) (β := Atom t) T p
    have hL : #{ℓ : V → Atom t | p (fun x => ℓ x)} =
        ∑ ℓ : V → Atom t, (if p (fun x => ℓ x) then (1 : ℕ) else 0) := by
      simp [sum_boole]
    have hPcard : #{g : {x // x ∈ T} → Atom t | p g} = circuitWeight t j := by
      let e : ({x // x ∈ T} → Atom t) ≃ (Fin j → Atom t) :=
        Equiv.arrowCongr T.equivFin (Equiv.refl _)
      have hEq : #{g : {x // x ∈ T} → Atom t | p g} =
          #{ψ : Fin j → Atom t | IsCircuitTuple (t := t) (decode ∘ ψ)} := by
        have heq' : Fintype.card {g : {x // x ∈ T} → Atom t // p g} =
            Fintype.card {ψ : Fin j → Atom t // IsCircuitTuple (t := t) (decode ∘ ψ)} := by
          refine Fintype.card_congr ?_
          exact {
            toFun := fun ⟨g, hg⟩ => ⟨e g, by
              change IsCircuitTuple (t := t) (decode ∘ e g)
              convert hg using 1
              funext i
              rfl⟩
            invFun := fun ⟨ψ, hψ⟩ => ⟨e.symm ψ, by
              change IsCircuitTuple (t := t)
                (fun i => decode (e.symm ψ (T.equivFin.symm i)))
              convert hψ using 1
              funext i
              simp [e, Equiv.arrowCongr_apply, Equiv.apply_symm_apply]⟩
            left_inv := fun ⟨g, _⟩ => Subtype.ext (Equiv.symm_apply_apply e g)
            right_inv := fun ⟨ψ, _⟩ => Subtype.ext (Equiv.apply_symm_apply e ψ) }
        simpa [Fintype.card_subtype] using heq'
      rw [hEq, card_atom_circuits t j ht]
    have hW := card_Atom t ht
    have hmain : #{ℓ : V → Atom t | p (fun x => ℓ x)} =
        circuitWeight t j * D t ^ (Fintype.card V - j) := by
      calc #{ℓ : V → Atom t | p (fun x => ℓ x)}
          = ∑ ℓ : V → Atom t, (if p (fun x => ℓ x) then (1 : ℕ) else 0) := hL
        _ = #{g : {x // x ∈ T} → Atom t | p g} *
              (Fintype.card (Atom t)) ^ (Fintype.card V - #T) := hsum
        _ = circuitWeight t j * D t ^ (Fintype.card V - j) := by
            rw [hPcard, hW]
    simpa [p] using hmain
  have hmean : meanB (fun ℓ : V → Atom t =>
      decide (IsCircuitTuple (t := t)
        (fun i : Fin j => decode (ℓ (T.equivFin.symm i))))) =
      (circuitWeight t j : ℚ) / (D t : ℚ) ^ j := by
    unfold meanB
    have hσ : (Fintype.card (V → Atom t) : ℚ) = (D t : ℚ) ^ Fintype.card V := by
      rw [Fintype.card_fun, card_Atom t ht]; push_cast; rfl
    have hjle : j ≤ Fintype.card V := by
      calc j = #T := rfl
        _ ≤ Fintype.card V := card_le_univ _
    have hpow : (D t : ℚ) ^ Fintype.card V =
        (D t : ℚ) ^ j * (D t : ℚ) ^ (Fintype.card V - j) := by
      rw [← pow_add, Nat.add_sub_cancel' hjle]
    have hDne : (D t : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt (D_pos t ht))
    have hpowne : (D t : ℚ) ^ (Fintype.card V - j) ≠ 0 := pow_ne_zero _ hDne
    simp only [decide_eq_true_eq]
    rw [hcount, hσ, hpow]
    push_cast
    field_simp [hDne, hpowne]
  rw [hmean]
  exact circuit_mean_le ht hj1 hj

/-! ## Capacity algebra (Sol (6) threshold) -/

lemma A_t_as_moment (t : ℕ) :
    A_t t = t * (t + 1) ^ (2 * (t + 1) + 1) * (εNat t) ^ (2 * (t + 1)) := by
  have h := A_t_eq t
  simp only [εNat]
  have h1 : 2 * (t + 1) + 1 = 2 * t + 3 := by omega
  have h2 : 2 * (t + 1) = 2 * t + 2 := by omega
  rw [h, h1, h2]

lemma nat_pow_cancel_s (n t : ℕ) (hn : (n : ℚ) ≠ 0) :
    (n : ℚ) ^ t * (n : ℚ) ^ (t + 1) = (n : ℚ) ^ (2 * (t + 1)) / n := by
  have hsum : t + (t + 1) = 2 * t + 1 := by omega
  have hexp : 2 * (t + 1) = (2 * t + 1) + 1 := by omega
  calc (n : ℚ) ^ t * n ^ (t + 1)
      = n ^ (t + (t + 1)) := (pow_add _ _ _).symm
    _ = n ^ (2 * t + 1) := by rw [hsum]
    _ = n ^ (2 * (t + 1)) / n := by
          have : (n : ℚ) ^ (2 * (t + 1)) = n ^ (2 * t + 1) * n := by
            rw [hexp, pow_succ]
          rw [this]; field_simp [hn]

lemma frac_eq_At_div_n (t n : ℕ) (hn : 0 < n) (hε : 0 < εNat t) :
    let s := t + 1
    let ε : ℚ := (1 : ℚ) / εNat t
    (t : ℚ) * (n : ℚ) ^ t * ((n : ℚ) ^ s * (s : ℚ) ^ (2 * s + 1) /
      ((ε * (n : ℚ)) ^ (2 * s))) =
      (A_t t : ℚ) / n := by
  intro s ε
  have hnne : (n : ℚ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hn)
  have hεNne : (εNat t : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hε)
  have hcancel := nat_pow_cancel_s n t hnne
  have hA : (t : ℚ) * ((t + 1 : ℕ) : ℚ) ^ (2 * (t + 1) + 1) *
      (εNat t : ℚ) ^ (2 * (t + 1)) = (A_t t : ℚ) := by
    exact_mod_cast (A_t_as_moment t).symm
  have hεpow : ((1 : ℚ) / εNat t) ^ (2 * (t + 1)) =
      (1 : ℚ) / (εNat t : ℚ) ^ (2 * (t + 1)) := by rw [div_pow, one_pow]
  show (t : ℚ) * n ^ t *
      (n ^ (t + 1) * ((t + 1 : ℕ) : ℚ) ^ (2 * (t + 1) + 1) /
        (((1 : ℚ) / εNat t) * n) ^ (2 * (t + 1))) = (A_t t : ℚ) / n
  have hden2 : (((1 : ℚ) / εNat t) * n) ^ (2 * (t + 1)) =
      ((1 : ℚ) / εNat t) ^ (2 * (t + 1)) * n ^ (2 * (t + 1)) := by ring
  rw [hden2, hεpow]
  have hmid : (t : ℚ) * n ^ t * (n ^ (t + 1) * ((t + 1 : ℕ) : ℚ) ^ (2 * (t + 1) + 1) /
        ((1 / (εNat t : ℚ) ^ (2 * (t + 1))) * n ^ (2 * (t + 1)))) =
      (t : ℚ) * ((t + 1 : ℕ) : ℚ) ^ (2 * (t + 1) + 1) *
        (εNat t : ℚ) ^ (2 * (t + 1)) / n := by
    have h1 : (t : ℚ) * n ^ t * (n ^ (t + 1) * ((t + 1 : ℕ) : ℚ) ^ (2 * (t + 1) + 1) /
          ((1 / (εNat t : ℚ) ^ (2 * (t + 1))) * n ^ (2 * (t + 1)))) =
        (t : ℚ) * ((t + 1 : ℕ) : ℚ) ^ (2 * (t + 1) + 1) * (n ^ t * n ^ (t + 1)) /
          (1 / (εNat t : ℚ) ^ (2 * (t + 1)) * n ^ (2 * (t + 1))) := by ring
    rw [h1, hcancel]
    field_simp [hnne, hεNne]
  rw [hmid, hA]

lemma frac_le_At_div_n {t n : ℕ} (ht : 2 ≤ t) (hn : 0 < n)
    (GoodCard : ℚ) (hG : GoodCard ≤ (t : ℚ) * (n : ℚ) ^ t) :
    let s := t + 1
    let ε : ℚ := (1 : ℚ) / εNat t
    GoodCard * ((n : ℚ) ^ s * (s : ℚ) ^ (2 * s + 1) / ((ε * n) ^ (2 * s))) ≤
      (A_t t : ℚ) / n := by
  intro s ε
  have hεpos : 0 < εNat t := εNat_pos (by omega)
  have hεQ : (0 : ℚ) < ε := one_div_pos.mpr (Nat.cast_pos.mpr hεpos)
  have hnQ : (0 : ℚ) < n := Nat.cast_pos.mpr hn
  have hden : (0 : ℚ) < (ε * n) ^ (2 * s) := pow_pos (mul_pos hεQ hnQ) _
  have h1 : GoodCard * ((n : ℚ) ^ s * (s : ℚ) ^ (2 * s + 1) / ((ε * n) ^ (2 * s))) ≤
      (t : ℚ) * (n : ℚ) ^ t * ((n : ℚ) ^ s * (s : ℚ) ^ (2 * s + 1) / ((ε * n) ^ (2 * s))) :=
    mul_le_mul_of_nonneg_right hG (div_nonneg
      (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (pow_nonneg (Nat.cast_nonneg _) _))
      (le_of_lt hden))
  exact h1.trans (le_of_eq (frac_eq_At_div_n t n hn hεpos))

lemma card_compl_finset {U : Type*} [Fintype U] [DecidableEq U] (B : Finset U) :
    Fintype.card {x : U // x ∉ B} = Fintype.card U - #B := by
  rw [Fintype.card_subtype]
  have h : univ.filter (fun x : U => x ∉ B) = univ \ B := by
    ext x; simp [mem_sdiff]
  rw [show #{x : U | x ∉ B} = #(univ.filter (fun x => x ∉ B)) from rfl, h, card_univ_sdiff]

lemma nonempty_compl_of_large {U : Type*} [Fintype U] [DecidableEq U]
    {t k : ℕ} (B : Finset U)
    (hU : Fintype.card U = 2 ^ k) (hB : #B = k - t)
    (_hk : t ≤ k) :
    Nonempty {x : U // x ∉ B} := by
  have : 0 < Fintype.card {x : U // x ∉ B} := by
    rw [card_compl_finset, hU, hB]
    have : k - t < 2 ^ k := Nat.lt_of_le_of_lt (Nat.sub_le k t) Nat.lt_two_pow_self
    omega
  exact Fintype.card_pos_iff.mp this

lemma sum_indB_eq_card {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    (f : σ → Bool) (ω : ι → σ) :
    ∑ i : ι, indB f (ω i) = (#{i : ι | f (ω i) = true} : ℚ) := by
  simp only [indB]
  have h : (∑ i : ι, (if f (ω i) = true then (1 : ℕ) else 0) : ℕ) =
      #{i : ι | f (ω i) = true} := by
    simp [sum_boole]
  have : ∑ i : ι, (if f (ω i) = true then (1 : ℚ) else 0) =
      ↑(∑ i : ι, (if f (ω i) = true then (1 : ℕ) else 0)) := by
    rw [Nat.cast_sum]; congr 1; ext i; split_ifs <;> simp
  rw [this, h]

/-! ## Capacity (Sol (6)) -/

theorem circuit_capacity_labellings
    {V U : Type*} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    [Nonempty U] [Nonempty V]
    {t : ℕ} (ht : 2 ≤ t)
    (hn : A_t t < Fintype.card U)
    (hV : Fintype.card V ≤ Fintype.card U) :
    ∃ v : U → V → E t,
      ∀ T : Finset V, T.Nonempty → #T ≤ t →
        #{u : U | IsCircuit (v u) T} ≤ Fintype.card U / q t := by
  classical
  let n := Fintype.card U
  have hnpos : (0 : ℕ) < n := Fintype.card_pos
  have hqpos : 0 < q t := lt_of_lt_of_le (by omega : 0 < 2) (q_ge_two ht)
  have hεpos : 0 < εNat t := εNat_pos (by omega)
  haveI : Nonempty (Atom t) := Atom_nonempty t ht
  let σ := V → Atom t
  haveI : Nonempty σ := ⟨fun _ => Classical.arbitrary (Atom t)⟩
  let s := t + 1
  have hs : 1 ≤ s := by omega
  let β : ℚ := (1 : ℚ) / q t
  let ε : ℚ := (1 : ℚ) / εNat t
  have hεQ : (0 : ℚ) < ε := one_div_pos.mpr (Nat.cast_pos.mpr hεpos)
  let GoodT := univ.filter (fun T : Finset V => T.Nonempty ∧ #T ≤ t)
  have hGoodCard : (#GoodT : ℚ) ≤ (t : ℚ) * (n : ℚ) ^ t := by
    have hnV : 0 < Fintype.card V := Fintype.card_pos
    have h1 := card_small_subsets V t hnV
    have : t * Fintype.card V ^ t ≤ t * n ^ t :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hV t)
    have hG : #GoodT = #{T : Finset V | T.Nonempty ∧ #T ≤ t} := by
      simp [GoodT]
    exact_mod_cast (hG ▸ h1).trans this
  let fT : Finset V → (σ → Bool) := fun T ℓ =>
    decide (IsCircuitTuple (t := t)
      (fun i : Fin #T => decode (ℓ (T.equivFin.symm i))))
  have hmeanT (T : Finset V) (hne : T.Nonempty) (hc : #T ≤ t) :
      meanB (fT T) ≤ β - ε := by
    simpa [fT, β, ε] using meanB_circuit ht hne hc
  let Lab := U → σ
  let Bad : Finset V → Finset Lab := fun T =>
    univ.filter (fun ω : Lab =>
      β * (Fintype.card U : ℚ) < ∑ u : U, indB (fT T) (ω u))
  have hbad_le (T : Finset V) (hne : T.Nonempty) (hc : #T ≤ t) :
      (#(Bad T) : ℚ) * (ε * (Fintype.card U : ℚ)) ^ (2 * s) ≤
        (Fintype.card U : ℚ) ^ s * (s : ℚ) ^ (2 * s + 1) *
          (Fintype.card σ : ℚ) ^ Fintype.card U := by
    have hm := hmeanT T hne hc
    have hmb := moment_bound_zero_one (σ := σ) (ι := U) (f := fT T) s hs β ε hεQ hm
    -- Bad T is definitionally the filter counted by moment_bound
    simpa [Bad, Lab] using hmb
  have hexists : ∃ ℓ : Lab, ∀ T ∈ GoodT, ℓ ∉ Bad T := by
    by_contra hnone
    push Not at hnone
    have hcover : ∀ ℓ : Lab, ∃ T ∈ GoodT, ℓ ∈ Bad T := hnone
    have hLab_le : (Fintype.card Lab : ℚ) ≤ ∑ T ∈ GoodT, (#(Bad T) : ℚ) := by
      have hsub : (univ : Finset Lab) ⊆ GoodT.biUnion Bad := by
        intro ℓ _
        obtain ⟨T, hT, hbad⟩ := hcover ℓ
        exact mem_biUnion.mpr ⟨T, hT, hbad⟩
      have : Fintype.card Lab ≤ ∑ T ∈ GoodT, #(Bad T) :=
        (card_le_card hsub).trans card_biUnion_le
      exact_mod_cast this
    have hbad_bound : ∀ T ∈ GoodT, (#(Bad T) : ℚ) ≤
        (n : ℚ) ^ s * (s : ℚ) ^ (2 * s + 1) * (Fintype.card σ : ℚ) ^ n /
          ((ε * n) ^ (2 * s)) := by
      intro T hT
      obtain ⟨hne, hc⟩ := (mem_filter.mp hT).2
      have hnε : (0 : ℚ) < ε * n := mul_pos hεQ (Nat.cast_pos.mpr hnpos)
      have hpow : (0 : ℚ) < (ε * n) ^ (2 * s) := pow_pos hnε _
      have h' : (#(Bad T) : ℚ) * (ε * n) ^ (2 * s) ≤
          (n : ℚ) ^ s * (s : ℚ) ^ (2 * s + 1) * (Fintype.card σ : ℚ) ^ n := by
        simpa [n] using hbad_le T hne hc
      exact (le_div_iff₀ hpow).2 h' 
    have hsum_bad : ∑ T ∈ GoodT, (#(Bad T) : ℚ) ≤
        (#GoodT : ℚ) *
          ((n : ℚ) ^ s * (s : ℚ) ^ (2 * s + 1) * (Fintype.card σ : ℚ) ^ n /
            ((ε * n) ^ (2 * s))) := by
      have := sum_le_card_nsmul GoodT (fun T => (#(Bad T) : ℚ)) _ hbad_bound
      simpa [nsmul_eq_mul] using this
    have hLab : (Fintype.card Lab : ℚ) = (Fintype.card σ : ℚ) ^ n := by
      simp only [Lab, n]
      rw [Fintype.card_fun]
      push_cast
      rfl
    have hσpos : (0 : ℚ) < (Fintype.card σ : ℚ) ^ n :=
      pow_pos (Nat.cast_pos.mpr Fintype.card_pos) _
    have hcomb : (Fintype.card σ : ℚ) ^ n ≤
        (#GoodT : ℚ) * ((n : ℚ) ^ s * (s : ℚ) ^ (2 * s + 1) *
          (Fintype.card σ : ℚ) ^ n / ((ε * n) ^ (2 * s))) := by
      calc (Fintype.card σ : ℚ) ^ n
          = (Fintype.card Lab : ℚ) := hLab.symm
        _ ≤ ∑ T ∈ GoodT, (#(Bad T) : ℚ) := hLab_le
        _ ≤ (#GoodT : ℚ) * ((n : ℚ) ^ s * (s : ℚ) ^ (2 * s + 1) *
              (Fintype.card σ : ℚ) ^ n / ((ε * n) ^ (2 * s))) := hsum_bad
    have hnε : (0 : ℚ) < ε * n := mul_pos hεQ (Nat.cast_pos.mpr hnpos)
    have hpow : (0 : ℚ) < (ε * n) ^ (2 * s) := pow_pos hnε _
    have hcancel : (1 : ℚ) ≤ (#GoodT : ℚ) *
        ((n : ℚ) ^ s * (s : ℚ) ^ (2 * s + 1) / ((ε * n) ^ (2 * s))) := by
      calc (1 : ℚ)
          = (Fintype.card σ : ℚ) ^ n / (Fintype.card σ : ℚ) ^ n := by
              field_simp [hσpos.ne']
        _ ≤ ((#GoodT : ℚ) * ((n : ℚ) ^ s * (s : ℚ) ^ (2 * s + 1) *
              (Fintype.card σ : ℚ) ^ n / ((ε * n) ^ (2 * s)))) /
              (Fintype.card σ : ℚ) ^ n :=
            div_le_div_of_nonneg_right hcomb (le_of_lt hσpos)
        _ = (#GoodT : ℚ) * ((n : ℚ) ^ s * (s : ℚ) ^ (2 * s + 1) / ((ε * n) ^ (2 * s))) := by
            field_simp [hσpos.ne', hpow.ne']
            try { ring }
    have hAt_bound := frac_le_At_div_n ht hnpos (#GoodT : ℚ) hGoodCard
    have hAt_lt : (A_t t : ℚ) / n < 1 := by
      have : (A_t t : ℚ) < n := by exact_mod_cast hn
      exact (div_lt_one (Nat.cast_pos.mpr hnpos)).2 this
    have : (1 : ℚ) < 1 := lt_of_le_of_lt hcancel (lt_of_le_of_lt hAt_bound hAt_lt)
    exact absurd this (lt_irrefl _)
  obtain ⟨ℓ, hℓ⟩ := hexists
  refine ⟨fun u x => decode (ℓ u x), ?_⟩
  intro T hne hc
  have hTmem : T ∈ GoodT := mem_filter.mpr ⟨mem_univ _, ⟨hne, hc⟩⟩
  have hnot : ℓ ∉ Bad T := hℓ T hTmem
  have hsumle : ∑ u : U, indB (fT T) (ℓ u) ≤ β * n := le_of_not_gt (by
    simpa [Bad, mem_filter] using hnot)
  have hsumEq : ∑ u : U, indB (fT T) (ℓ u) =
      (#{u : U | fT T (ℓ u) = true} : ℚ) := sum_indB_eq_card (fT T) ℓ
  have htupleQ : (#{u : U | IsCircuitTuple (t := t)
      (fun i : Fin #T => decode (ℓ u (T.equivFin.symm i)))} : ℚ) ≤ (n : ℚ) / q t := by
    have hfeq : #{u : U | fT T (ℓ u) = true} =
        #{u : U | IsCircuitTuple (t := t)
          (fun i : Fin #T => decode (ℓ u (T.equivFin.symm i)))} := by
      simp only [fT, decide_eq_true_eq]
    have hβ : β * n = (n : ℚ) / q t := by
      simp only [β]; field_simp
    rw [← hfeq, ← hsumEq, ← hβ]
    exact hsumle
  have htuple_card : #{u : U | IsCircuitTuple (t := t)
      (fun i : Fin #T => decode (ℓ u (T.equivFin.symm i)))} ≤ n / q t := by
    have hq0 : (0 : ℚ) < q t := Nat.cast_pos.mpr hqpos
    have hmul : #{u : U | IsCircuitTuple (t := t)
        (fun i => decode (ℓ u (T.equivFin.symm i)))} * q t ≤ n := by
      exact_mod_cast (le_div_iff₀ hq0).1 htupleQ
    exact Nat.le_div_iff_mul_le hqpos |>.2 hmul
  refine le_trans ?_ htuple_card
  refine card_le_card ?_
  intro u hu
  have hC : IsCircuit (fun x => decode (ℓ u x)) T := (mem_filter.mp hu).2
  exact mem_filter.mpr ⟨mem_univ _,
    isCircuit_to_tuple (T.equivFin.symm) (fun x => decode (ℓ u x))
      (Nat.succ_le_of_lt (card_pos.mpr hne)) rfl hC⟩

/-- Main theorem: Sol (1)+(2). Does **not** settle PAIR/#624. -/
theorem growing_core_obstruction
    {U : Type*} [Fintype U] [DecidableEq U]
    {t k : ℕ} (ht : 2 ≤ t) (hk : t ≤ k) (hkk : 16 * (t + 1) ^ 2 ≤ k)
    (hU : Fintype.card U = 2 ^ k)
    (B : Finset U) (hB : #B = k - t) :
    ∃ (g0 g1 : Finset U → U),
      ∀ Y : Finset U, #Y = k → B ⊆ Y →
        (Y.powerset.image g0 ∪ Y.powerset.image g1) = (univ : Finset U) := by
  haveI : Nonempty U := by
    rw [← Fintype.card_pos_iff, hU]; exact Nat.two_pow_pos _
  have hn : A_t t < 2 ^ k := pow_k_gt_A_t ht hkk
  have hnU : A_t t < Fintype.card U := by simpa [hU] using hn
  let V := {x : U // x ∉ B}
  have hVle : Fintype.card V ≤ Fintype.card U := by
    rw [card_compl_finset]; exact Nat.sub_le _ _
  haveI : Nonempty V := nonempty_compl_of_large B hU hB hk
  obtain ⟨v, hcap⟩ := circuit_capacity_labellings (V := V) (U := U) ht hnU hVle
  have hcap' : ∀ T : Finset V, T.Nonempty → #T ≤ t →
      #{u : U | IsCircuit (v u) T} ≤ 2 ^ k / q t := by
    intro T hne hc; simpa [hU] using hcap T hne hc
  have hcover : ∀ Z : Finset V, #Z = t → ∀ u : U, ∃ T ⊆ Z, IsCircuit (v u) T := by
    intro Z hZ u
    exact exists_circuit_of_card (by omega : 1 ≤ t) (v u) Z hZ
  exact maps_from_capacity ht hk hU B hB v hcap' hcover

end E624R8


namespace Erdos624

open Finset

/-- Growing-core / prescribed-star integral obstruction (Sol (1)+(2)).
For `t ≥ 2` and `k ≥ 16(t+1)^2`, every `(k−t)`-set `B ⊆ U` (`|U|=2^k`) admits maps
`g₀,g₁` covering `U` on every `k`-set in the star of `B`.
Does **not** settle PAIR / #624. -/
theorem growing_core_obstruction
    {U : Type*} [Fintype U] [DecidableEq U]
    {t k : ℕ} (ht : 2 ≤ t) (hk : t ≤ k) (hkk : 16 * (t + 1) ^ 2 ≤ k)
    (hU : Fintype.card U = 2 ^ k)
    (B : Finset U) (hB : #B = k - t) :
    ∃ (g0 g1 : Finset U → U),
      ∀ Y : Finset U, #Y = k → B ⊆ Y →
        (Y.powerset.image g0 ∪ Y.powerset.image g1) = (univ : Finset U) :=
  E624R8.growing_core_obstruction ht hk hkk hU B hB

end Erdos624

open Finset

theorem solution
    {U : Type*} [Fintype U] [DecidableEq U]
    {t k : ℕ} (ht : 2 ≤ t) (hk : t ≤ k) (hkk : 16 * (t + 1) ^ 2 ≤ k)
    (hU : Fintype.card U = 2 ^ k)
    (B : Finset U) (hB : #B = k - t) :
    ∃ (g0 g1 : Finset U → U),
      ∀ Y : Finset U, #Y = k → B ⊆ Y →
        (Y.powerset.image g0 ∪ Y.powerset.image g1) = (univ : Finset U) :=
  Erdos624.growing_core_obstruction ht hk hkk hU B hB

#print axioms solution
#print axioms Erdos624.growing_core_obstruction
