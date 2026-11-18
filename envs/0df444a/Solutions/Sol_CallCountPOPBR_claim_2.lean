-- Prove2me | solution 1 for CallCountPOPBR.claim_2
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-17T15:39:08.481384+00:00
-- url     : https://prove2.me/submissions/68d79b20-77de-4983-bb7f-1a98fa70ccd1

import Definitions.Def_CallCountPOPBR_wt
import Definitions.Def_CallCountPOPBR_part

set_option autoImplicit false

namespace CL2Aux
open CallCountPOPBR

def bv (x i : ℕ) : ℕ := if x.testBit i then 2 ^ i else 0

lemma wt_rec (n : ℕ) : wt n = n % 2 + wt (n / 2) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [wt]
  · unfold wt
    rw [Nat.digits_def' (by norm_num) hn, List.sum_cons]

lemma wt_pos : ∀ x, 0 < x → 1 ≤ wt x := by
  intro x
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    intro hx
    rw [wt_rec]
    rcases Nat.mod_two_eq_zero_or_one x with h | h
    · have := ih (x / 2) (by omega) (by omega); omega
    · omega

lemma mod_succ (x g : ℕ) : x % 2 ^ (g + 1) = x % 2 ^ g + bv x g := by
  rw [Nat.mod_pow_succ, bv, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ g) with h | h <;> simp [h]

lemma mod_add_range (x a k : ℕ) :
    x % 2 ^ (a + k) = x % 2 ^ a + ∑ i ∈ Finset.Ico a (a + k), bv x i := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← add_assoc, mod_succ, ih, Finset.sum_Ico_succ_top (by omega), add_assoc]

lemma part_eq (R q x : ℕ) : part R q x + x % 2 ^ (q - R) = x % 2 ^ (q + 1) := by
  have h := mod_add_range x (q - R) (q + 1 - (q - R))
  rw [show q - R + (q + 1 - (q - R)) = q + 1 by omega] at h
  rw [h, part, add_comm]
  congr 1

lemma no_bits (x a b : ℕ) (hab : a ≤ b) (h : ∀ i, a ≤ i → i < b → x.testBit i = false) :
    x % 2 ^ b = x % 2 ^ a := by
  have := mod_add_range x a (b - a)
  rw [show a + (b - a) = b by omega] at this
  rw [this, Finset.sum_eq_zero]
  · simp
  · intro i hi
    rw [Finset.mem_Ico] at hi
    simp [bv, h i hi.1 (by omega)]

lemma bit_le_mod (x i g : ℕ) (hi : i < g) (hb : x.testBit i = true) : 2 ^ i ≤ x % 2 ^ g := by
  have := mod_add_range x i (g - i)
  rw [show i + (g - i) = g by omega] at this
  rw [this]
  have : bv x i ≤ ∑ j ∈ Finset.Ico i g, bv x j :=
    Finset.single_le_sum (f := bv x) (fun _ _ => Nat.zero_le _) (by simp; omega)
  have hbv : bv x i = 2 ^ i := by simp [bv, hb]
  rw [hbv] at this
  omega

lemma card_filter_le_wt : ∀ x (T : Finset ℕ), (T.filter (fun i => x.testBit i = true)).card ≤ wt x := by
  intro x
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    intro T
    rcases Nat.eq_zero_or_pos x with rfl | hx
    · simp
    have hsub : T.filter (fun i => x.testBit i = true) ⊆
        (if x % 2 = 1 then ({0} : Finset ℕ) else ∅) ∪
          (((T.image (· - 1)).filter (fun j => (x / 2).testBit j = true)).image (· + 1)) := by
      intro i hi
      rw [Finset.mem_filter] at hi
      rw [Finset.mem_union]
      rcases Nat.eq_zero_or_pos i with rfl | hipos
      · left
        rw [Nat.testBit_zero] at hi
        have : x % 2 = 1 := by simpa using hi.2
        simp [this]
      · right
        rw [Finset.mem_image]
        refine ⟨i - 1, ?_, by omega⟩
        rw [Finset.mem_filter, Finset.mem_image]
        refine ⟨⟨i, hi.1, rfl⟩, ?_⟩
        have := hi.2
        rw [show i = (i - 1).succ by omega, Nat.testBit_succ] at this
        exact this
    calc (T.filter (fun i => x.testBit i = true)).card
        ≤ ((if x % 2 = 1 then ({0} : Finset ℕ) else ∅) ∪
          (((T.image (· - 1)).filter (fun j => (x / 2).testBit j = true)).image (· + 1))).card :=
          Finset.card_le_card hsub
      _ ≤ (if x % 2 = 1 then ({0} : Finset ℕ) else ∅).card +
          (((T.image (· - 1)).filter (fun j => (x / 2).testBit j = true)).image (· + 1)).card :=
          Finset.card_union_le _ _
      _ ≤ x % 2 + wt (x / 2) := by
          apply Nat.add_le_add
          · split_ifs with h <;> simp [h]
          · exact Finset.card_image_le.trans (ih (x / 2) (by omega) _)
      _ = wt x := (wt_rec x).symm

/-- low part of 2^q₁+2^q₂+2^q₃ below 2^g -/
def low (q₁ q₂ q₃ g : ℕ) : ℕ :=
  (if q₁ < g then 2 ^ q₁ else 0) + (if q₂ < g then 2 ^ q₂ else 0) + (if q₃ < g then 2 ^ q₃ else 0)

lemma two_pow_lt_of_lt {a b : ℕ} (h : a < b) : 2 * 2 ^ a ≤ 2 ^ b := by
  rw [← pow_succ']; exact Nat.pow_le_pow_right (by norm_num) h

lemma low_lt (q₁ q₂ q₃ g : ℕ) (h12 : q₂ < q₁) (h23 : q₃ < q₂) : low q₁ q₂ q₃ g < 2 ^ g := by
  have a12 := two_pow_lt_of_lt h12
  have a23 := two_pow_lt_of_lt h23
  have p3 : 0 < 2 ^ q₃ := by positivity
  have pg : 0 < 2 ^ g := by positivity
  unfold low
  split_ifs with c1 c2 c3 c3 c2 c3 c3
  all_goals first
    | (have := two_pow_lt_of_lt c1; omega)
    | (have := two_pow_lt_of_lt c2; omega)
    | (have := two_pow_lt_of_lt c3; omega)
    | omega

lemma modQ (q₁ q₂ q₃ g : ℕ) (h12 : q₂ < q₁) (h23 : q₃ < q₂) :
    (2 ^ q₁ + 2 ^ q₂ + 2 ^ q₃) % 2 ^ g = low q₁ q₂ q₃ g := by
  have e : ∀ q, 2 ^ q = (if q < g then 2 ^ q else 0) + 2 ^ g * (if q < g then 0 else 2 ^ (q - g)) := by
    intro q
    split_ifs with h
    · simp
    · rw [zero_add, ← pow_add]; congr 1; omega
  have : 2 ^ q₁ + 2 ^ q₂ + 2 ^ q₃ = low q₁ q₂ q₃ g + 2 ^ g *
      ((if q₁ < g then 0 else 2 ^ (q₁ - g)) + (if q₂ < g then 0 else 2 ^ (q₂ - g)) +
        (if q₃ < g then 0 else 2 ^ (q₃ - g))) := by
    conv_lhs => rw [e q₁, e q₂, e q₃]
    unfold low; ring
  rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (low_lt q₁ q₂ q₃ g h12 h23)]

end CL2Aux

open CallCountPOPBR CL2Aux in
theorem solution (q₁ q₂ q₃ R u v : ℕ) (h₁₂ : q₂ + 2 * R + 2 ≤ q₁) (h₂₃ : q₃ + 2 * R + 2 ≤ q₂)
    (hu : 0 < u) (hv : 0 < v) (huv : u + v = 2 ^ q₁ + 2 ^ q₂ + 2 ^ q₃)
    (hwt : wt u + wt v ≤ R) :
    (∀ i, (u.testBit i = true ∨ v.testBit i = true) →
      ∃ q ∈ ({q₁, q₂, q₃} : Finset ℕ), q ≤ i + R ∧ i ≤ q) ∧
    (∀ q ∈ ({q₁, q₂, q₃} : Finset ℕ), part R q u + part R q v = 2 ^ q) ∧
    (∀ q ∈ ({q₁, q₂, q₃} : Finset ℕ),
      ∃ i, q ≤ i + R ∧ i ≤ q ∧ (u.testBit i = true ∨ v.testBit i = true)) := by
  have hR : 2 ≤ R := by have := wt_pos u hu; have := wt_pos v hv; omega
  have h12 : q₂ < q₁ := by omega
  have h23 : q₃ < q₂ := by omega
  -- sum mod a cut
  have hcut : ∀ g, u % 2 ^ g + v % 2 ^ g < 2 ^ g →
      u % 2 ^ g + v % 2 ^ g = low q₁ q₂ q₃ g := by
    intro g hg
    rw [← modQ q₁ q₂ q₃ g h12 h23, ← huv, Nat.add_mod, Nat.mod_eq_of_lt hg]
  -- Part A
  have partA : ∀ i, (u.testBit i = true ∨ v.testBit i = true) →
      ∃ q ∈ ({q₁, q₂, q₃} : Finset ℕ), q ≤ i + R ∧ i ≤ q := by
    intro i hi
    by_contra hno
    push Not at hno
    have n1 : q₁ ≤ i + R → q₁ < i := hno q₁ (by simp)
    have n2 : q₂ ≤ i + R → q₂ < i := hno q₂ (by simp)
    have n3 : q₃ ≤ i + R → q₃ < i := hno q₃ (by simp)
    have hg : ∃ g, i + 1 ≤ g ∧ g ≤ i + R + 1 ∧ u % 2 ^ g + v % 2 ^ g < 2 ^ g := by
      by_contra hall
      push Not at hall
      have hbits : ∀ j, i ≤ j → j ≤ i + R → (u.testBit j = true ∨ v.testBit j = true) := by
        intro j hj1 hj2
        rcases Nat.eq_or_lt_of_le hj1 with rfl | hj1
        · exact hi
        by_contra hb
        push Not at hb
        simp only [ne_eq, Bool.not_eq_true] at hb
        have e1 := mod_succ u j
        have e2 := mod_succ v j
        simp only [bv, hb.1, hb.2] at e1 e2
        have m1 := Nat.mod_lt u (show 0 < 2 ^ j by positivity)
        have m2 := Nat.mod_lt v (show 0 < 2 ^ j by positivity)
        have := hall (j + 1) (by omega) (by omega)
        have p : 2 ^ (j + 1) = 2 * 2 ^ j := by ring
        simp at e1 e2
        omega
      have hT : Finset.Icc i (i + R) ⊆ (Finset.Icc i (i + R)).filter (fun j => u.testBit j = true) ∪
          (Finset.Icc i (i + R)).filter (fun j => v.testBit j = true) := by
        intro j hj
        have hj' := Finset.mem_Icc.1 hj
        rcases hbits j hj'.1 hj'.2 with h | h
        · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hj, h⟩)
        · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hj, h⟩)
      have := (Finset.card_le_card hT).trans (Finset.card_union_le _ _)
      have c1 := card_filter_le_wt u (Finset.Icc i (i + R))
      have c2 := card_filter_le_wt v (Finset.Icc i (i + R))
      simp only [Nat.card_Icc] at this
      omega
    obtain ⟨g, hg1, hg2, hg3⟩ := hg
    have hlow := hcut g hg3
    have hge : 2 ^ i ≤ u % 2 ^ g + v % 2 ^ g := by
      rcases hi with h | h
      · have := bit_le_mod u i g (by omega) h; omega
      · have := bit_le_mod v i g (by omega) h; omega
    have hli : low q₁ q₂ q₃ g = low q₁ q₂ q₃ i := by
      unfold low
      have a1 : q₁ < g ↔ q₁ < i := ⟨fun h => n1 (by omega), fun h => by omega⟩
      have a2 : q₂ < g ↔ q₂ < i := ⟨fun h => n2 (by omega), fun h => by omega⟩
      have a3 : q₃ < g ↔ q₃ < i := ⟨fun h => n3 (by omega), fun h => by omega⟩
      simp only [a1, a2, a3]
    have := low_lt q₁ q₂ q₃ i h12 h23
    omega
  -- Part B
  have partB : ∀ q ∈ ({q₁, q₂, q₃} : Finset ℕ), part R q u + part R q v = 2 ^ q := by
    intro q hq
    have hq' : q = q₁ ∨ q = q₂ ∨ q = q₃ := by simpa using hq
    -- no bits just above the window
    have top : ∀ x, (x = u ∨ x = v) → x % 2 ^ (q + R + 1) = x % 2 ^ (q + 1) := by
      intro x hx
      apply no_bits x _ _ (by omega)
      intro i hi1 hi2
      by_contra hb
      simp only [Bool.not_eq_false] at hb
      have hb' : u.testBit i = true ∨ v.testBit i = true := by
        rcases hx with rfl | rfl
        · exact Or.inl hb
        · exact Or.inr hb
      obtain ⟨q', hq'm, h1, h2⟩ := partA i hb'
      have : q' = q₁ ∨ q' = q₂ ∨ q' = q₃ := by simpa using hq'm
      omega
    have bot : ∀ x, (x = u ∨ x = v) → x % 2 ^ (q - R) = x % 2 ^ ((q - R) - (R + 1)) := by
      intro x hx
      apply no_bits x _ _ (by omega)
      intro i hi1 hi2
      by_contra hb
      simp only [Bool.not_eq_false] at hb
      have hb' : u.testBit i = true ∨ v.testBit i = true := by
        rcases hx with rfl | rfl
        · exact Or.inl hb
        · exact Or.inr hb
      obtain ⟨q', hq'm, h1, h2⟩ := partA i hb'
      have : q' = q₁ ∨ q' = q₂ ∨ q' = q₃ := by simpa using hq'm
      omega
    have tu := top u (Or.inl rfl)
    have tv := top v (Or.inr rfl)
    have bu := bot u (Or.inl rfl)
    have bv' := bot v (Or.inr rfl)
    have St : u % 2 ^ (q + R + 1) + v % 2 ^ (q + R + 1) < 2 ^ (q + R + 1) := by
      rw [tu, tv]
      have m1 := Nat.mod_lt u (show 0 < 2 ^ (q + 1) by positivity)
      have m2 := Nat.mod_lt v (show 0 < 2 ^ (q + 1) by positivity)
      have := two_pow_lt_of_lt (show q + 1 < q + R + 1 by omega)
      omega
    have Sb : u % 2 ^ (q - R) + v % 2 ^ (q - R) < 2 ^ (q - R) := by
      rw [bu, bv']
      rcases Nat.eq_zero_or_pos ((q - R) - (R + 1)) with h0 | hpos
      · rw [h0]; simp only [pow_zero, Nat.mod_one]; positivity
      · have m1 := Nat.mod_lt u (show 0 < 2 ^ ((q - R) - (R + 1)) by positivity)
        have m2 := Nat.mod_lt v (show 0 < 2 ^ ((q - R) - (R + 1)) by positivity)
        have := two_pow_lt_of_lt (show (q - R) - (R + 1) < q - R by omega)
        omega
    have Lt := hcut _ St
    have Lb := hcut _ Sb
    have pu := part_eq R q u
    have pv := part_eq R q v
    have hdiff : low q₁ q₂ q₃ (q + R + 1) = low q₁ q₂ q₃ (q - R) + 2 ^ q := by
      unfold low
      rcases hq' with rfl | rfl | rfl <;> split_ifs <;> omega
    omega
  refine ⟨partA, partB, ?_⟩
  intro q hq
  by_contra hno
  push Not at hno
  have hB := partB q hq
  have z : ∀ x, (x = u ∨ x = v) → part R q x = 0 := by
    intro x hx
    unfold part
    apply Finset.sum_eq_zero
    intro i hi
    rw [Finset.mem_Icc] at hi
    have := hno i (by omega) hi.2
    rcases hx with rfl | rfl
    · simp [this.1]
    · simp [this.2]
  rw [z u (Or.inl rfl), z v (Or.inr rfl)] at hB
  have : 0 < 2 ^ q := by positivity
  omega
