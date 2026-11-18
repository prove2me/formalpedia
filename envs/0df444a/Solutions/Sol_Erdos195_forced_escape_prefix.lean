-- Prove2me | solution 1 for Erdos195.forced_escape_prefix
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-17T16:30:20.147661+00:00
-- url     : https://prove2.me/submissions/dfef35d8-96d6-4c0a-bd56-e2ec3f339407

import Definitions.Def_Erdos195_tree
import Theorems.Thm_Erdos195_odd_entry_demand
import Theorems.Thm_Erdos195_treeLt_safe_iff
import Mathlib.Data.List.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false

namespace Erdos195

private lemma instPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

private lemma x_form {x : ℤ} (hxmod : x % 4 = 3) : x = 4 * (x / 4) + 3 := by
  have h := Int.ediv_mul_add_emod x 4
  -- `x / 4 * 4 + x % 4 = x`
  rw [hxmod, mul_comm] at h
  linarith

private lemma x_odd {x : ℤ} (hxmod : x % 4 = 3) : x % 2 = 1 := by
  have hx := x_form hxmod
  omega

private lemma idxOf_zero (x : ℤ) (T : List ℤ) :
    (0 :: 1 :: x :: T).idxOf 0 = 0 := rfl

private lemma idxOf_one (x : ℤ) (T : List ℤ) :
    (0 :: 1 :: x :: T).idxOf 1 = 1 := by
  have hne : (0 : ℤ) ≠ 1 := by decide
  simp [List.idxOf_cons, beq_iff_eq, hne]

private lemma idxOf_x (x : ℤ) (T : List ℤ) (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    (0 :: 1 :: x :: T).idxOf x = 2 := by
  have h0 : (0 :: 1 :: x :: T).idxOf x = (1 :: x :: T).idxOf x + 1 :=
    List.idxOf_cons_ne _ hx0.symm
  have h1 : (1 :: x :: T).idxOf x = (x :: T).idxOf x + 1 :=
    List.idxOf_cons_ne _ hx1.symm
  have h2 : (x :: T).idxOf x = 0 := List.idxOf_cons_self
  omega

private lemma mem_tail_of_ne {x y : ℤ} {T : List ℤ}
    (hm : y ∈ 0 :: 1 :: x :: T) (hy0 : y ≠ 0) (hy1 : y ≠ 1) (hyx : y ≠ x) :
    y ∈ T := by
  simp [hy0, hy1, hyx] at hm
  exact hm

private lemma idxOf_gt_x {x y : ℤ} {T : List ℤ}
    (hm : y ∈ 0 :: 1 :: x :: T) (hy0 : y ≠ 0) (hy1 : y ≠ 1) (hyx : y ≠ x)
    (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    (0 :: 1 :: x :: T).idxOf x < (0 :: 1 :: x :: T).idxOf y := by
  have hyT : y ∈ T := mem_tail_of_ne hm hy0 hy1 hyx
  have hxidx : (0 :: 1 :: x :: T).idxOf x = 2 := idxOf_x x T hx0 hx1
  have h0 : (0 :: 1 :: x :: T).idxOf y = (1 :: x :: T).idxOf y + 1 :=
    List.idxOf_cons_ne _ hy0.symm
  have h1 : (1 :: x :: T).idxOf y = (x :: T).idxOf y + 1 :=
    List.idxOf_cons_ne _ hy1.symm
  have h2 : (x :: T).idxOf y = T.idxOf y + 1 :=
    List.idxOf_cons_ne _ hyx.symm
  have hlt : T.idxOf y < T.length := List.idxOf_lt_length_of_mem hyT
  omega

private lemma idxOf_eq_of_mem {Q : List ℤ} {a b : ℤ}
    (ha : a ∈ Q) (_hb : b ∈ Q) (h : Q.idxOf a = Q.idxOf b) : a = b :=
  (List.idxOf_inj ha).1 h

private lemma val_x_sub_one {x : ℤ} (hxmod : x % 4 = 3) :
    padicValInt 2 (x - 1) = 1 := by
  haveI := instPrimeTwo
  have hx := x_form hxmod
  have hx1 : x - 1 = 2 * (2 * (x / 4) + 1) := by omega
  have hodd : ¬ (2 : ℤ) ∣ 2 * (x / 4) + 1 := by
    intro h
    have : (2 * (x / 4) + 1) % 2 = 0 := Int.emod_eq_zero_of_dvd h
    omega
  have hne : 2 * (x / 4) + 1 ≠ 0 := by omega
  have hmul := padicValInt.mul (p := 2) (a := (2 : ℤ)) (b := 2 * (x / 4) + 1)
    (by decide) hne
  have h2 : padicValInt 2 (2 : ℤ) = 1 := padicValInt_self (p := 2)
  have h0 : padicValInt 2 (2 * (x / 4) + 1) = 0 :=
    padicValInt.eq_zero_of_not_dvd hodd
  rw [hx1, hmul, h2, h0]

private lemma val_two_x {x : ℤ} (hxmod : x % 4 = 3) :
    padicValInt 2 (2 * x) = 1 := by
  haveI := instPrimeTwo
  have hx := x_form hxmod
  have hx0 : x ≠ 0 := by omega
  have hodd : ¬ (2 : ℤ) ∣ x := by
    intro h
    have : x % 2 = 0 := Int.emod_eq_zero_of_dvd h
    omega
  have hmul := padicValInt.mul (p := 2) (a := (2 : ℤ)) (b := x) (by decide) hx0
  have h2 : padicValInt 2 (2 : ℤ) = 1 := padicValInt_self (p := 2)
  have h0 : padicValInt 2 x = 0 := padicValInt.eq_zero_of_not_dvd hodd
  rw [hmul, h2, h0]

private lemma val_three_x_sub_x {x : ℤ} (hxmod : x % 4 = 3) :
    padicValInt 2 (3 * x - x) = 1 := by
  have h : 3 * x - x = 2 * x := by ring
  rw [h, val_two_x hxmod]

private lemma bitOne_x {x : ℤ} (hxmod : x % 4 = 3) : bitOne x 1 := by
  unfold bitOne
  simp only [pow_one]
  have hx := x_form hxmod
  omega

private lemma not_bitOne_three_x {x : ℤ} (hxmod : x % 4 = 3) : ¬ bitOne (3 * x) 1 := by
  unfold bitOne
  simp only [pow_one]
  have hx := x_form hxmod
  omega

/-- If `2x` occurs in a word beginning `(0,1,x)`, it occurs after `x`. -/
private lemma two_x_after {x : ℤ} {T : List ℤ} (hx : (3 : ℤ) ≤ x)
    (hmem : 2 * x ∈ 0 :: 1 :: x :: T) :
    (0 :: 1 :: x :: T).idxOf x < (0 :: 1 :: x :: T).idxOf (2 * x) := by
  refine idxOf_gt_x hmem (by omega) (by omega) (by omega) (by omega) (by omega)

private lemma three_x_mem (θ : ℕ → ℤ → Bool) (Q : List ℤ) (x : ℤ)
    (hx : (3 : ℤ) ≤ x) (hxmod : x % 4 = 3)
    (hS : Safe (treeLt θ) Q)
    (hQ : ∃ T, Q = 0 :: 1 :: x :: T)
    (hrel : ∀ a b : ℤ, a ∈ Q → b ∈ Q → Q.idxOf a < Q.idxOf b → 2 * b - a ∉ Q →
      3 * b - 2 * a ∉ Q → (b - a) % 2 = 1 → b % 2 = 0) :
    3 * x ∈ Q := by
  obtain ⟨T, hQ⟩ := hQ
  have hhead : Q.head? = some 0 := by simp [hQ]
  have hxmem : x ∈ Q := by simp [hQ]
  have hxodd : x % 2 = 1 := x_odd hxmod
  have hdem := (odd_entry_demand θ Q hS hhead hrel).1 x hxmem hxodd
  rcases hdem.1 with h2x | h3x
  · by_contra h3x
    have hbefore := hdem.2 h3x
    have : Q.idxOf x < Q.idxOf (2 * x) := by
      simpa [hQ] using two_x_after (x := x) (T := T) hx (by simpa [hQ] using hbefore.1)
    exact lt_irrefl _ (hbefore.2.trans this)
  · exact h3x

private lemma not_both_open (θ : ℕ → ℤ → Bool) (Q : List ℤ) (x : ℤ)
    (hx : (3 : ℤ) ≤ x) (hxmod : x % 4 = 3)
    (hS : Safe (treeLt θ) Q)
    (hQ : ∃ T, Q = 0 :: 1 :: x :: T)
    (h3x : 3 * x ∈ Q)
    (hA2 : 2 * x - 1 ∉ Q) (hA3 : 3 * x - 2 ∉ Q)
    (hB2 : 5 * x ∉ Q) (hB3 : 7 * x ∉ Q) : False := by
  obtain ⟨T, hQ⟩ := hQ
  have h1mem : (1 : ℤ) ∈ Q := by simp [hQ]
  have hxmem : x ∈ Q := by simp [hQ]
  have hx0 : x ≠ 0 := by omega
  have hx1 : x ≠ 1 := by omega
  have idxx_lt : Q.idxOf x < Q.idxOf (3 * x) := by
    simpa [hQ] using
      (idxOf_gt_x (x := x) (y := 3 * x) (T := T) (by simpa [hQ] using h3x)
        (by omega) (by omega) (by omega) hx0 hx1)
  have hopen := ((treeLt_safe_iff θ Q).mp hS).2
  have hA := hopen (1 : ℤ) x h1mem hxmem (by
    have : Q.idxOf 1 = 1 := by simpa [hQ] using idxOf_one x T
    have : Q.idxOf x = 2 := by simpa [hQ] using idxOf_x x T hx0 hx1
    omega) (by simpa using hA2) (by simpa using hA3)
  have hB := hopen x (3 * x) hxmem h3x idxx_lt (by
    have : 2 * (3 * x) - x = 5 * x := by ring
    simpa [this] using hB2) (by
    have : 3 * (3 * x) - 2 * x = 7 * x := by ring
    simpa [this] using hB3)
  have hvalA : padicValInt 2 (x - 1) = 1 := val_x_sub_one hxmod
  have hvalB : padicValInt 2 (3 * x - x) = 1 := val_three_x_sub_x hxmod
  have hA' : θ 1 1 = true ↔ bitOne x 1 := by
    simpa [hvalA, pow_one] using hA
  have hB' : θ 1 1 = true ↔ bitOne (3 * x) 1 := by
    have hxodd : x % 2 = 1 := x_odd hxmod
    simpa [hvalB, pow_one, hxodd] using hB
  have htrue : θ 1 1 = true := (hA').2 (bitOne_x hxmod)
  have hfalse : θ 1 1 = false := by
    have hbit : ¬ bitOne (3 * x) 1 := not_bitOne_three_x hxmod
    cases hθ : θ 1 1 with
    | false => rfl
    | true =>
      have : bitOne (3 * x) 1 := (hB').1 hθ
      exact (hbit this).elim
  simp [htrue] at hfalse

private lemma two_x_sub_one_not_mem (θ : ℕ → ℤ → Bool) (Q : List ℤ) (x : ℤ)
    (hx : (3 : ℤ) ≤ x)
    (hS : Safe (treeLt θ) Q)
    (hQ : ∃ T, Q = 0 :: 1 :: x :: T)
    (h32 : 3 * x - 2 ∉ Q) : 2 * x - 1 ∉ Q := by
  obtain ⟨T, hQ⟩ := hQ
  intro hm
  have h1mem : (1 : ℤ) ∈ Q := by simp [hQ]
  have hxmem : x ∈ Q := by simp [hQ]
  have hx0 : x ≠ 0 := by omega
  have hx1 : x ≠ 1 := by omega
  have hlt : Q.idxOf x < Q.idxOf (2 * x - 1) := by
    simpa [hQ] using
      (idxOf_gt_x (x := x) (y := 2 * x - 1) (T := T) (by simpa [hQ] using hm)
        (by omega) (by omega) (by omega) hx0 hx1)
  have hidx : Q.idxOf (1 : ℤ) < Q.idxOf x := by
    have : Q.idxOf 1 = 1 := by simpa [hQ] using idxOf_one x T
    have : Q.idxOf x = 2 := by simpa [hQ] using idxOf_x x T hx0 hx1
    omega
  have hcont := ((treeLt_safe_iff θ Q).mp hS).1
  have h := hcont (1 : ℤ) x h1mem hxmem (by simpa using hm) hidx (by simpa using hlt)
  have : 3 * x - 2 * (1 : ℤ) ∈ Q := h.1
  exact h32 (by simpa using this)

private lemma five_before_three (θ : ℕ → ℤ → Bool) (Q : List ℤ) (x : ℤ)
    (hx : (3 : ℤ) ≤ x) (hxmod : x % 4 = 3)
    (hS : Safe (treeLt θ) Q)
    (hQ : ∃ T, Q = 0 :: 1 :: x :: T)
    (h3x : 3 * x ∈ Q) (h5 : 5 * x ∈ Q) (h7 : 7 * x ∉ Q) :
    Q.idxOf (5 * x) < Q.idxOf (3 * x) := by
  obtain ⟨T, hQ⟩ := hQ
  have hxmem : x ∈ Q := by simp [hQ]
  have hx0 : x ≠ 0 := by omega
  have hx1 : x ≠ 1 := by omega
  have idxx_lt : Q.idxOf x < Q.idxOf (3 * x) := by
    simpa [hQ] using
      (idxOf_gt_x (x := x) (y := 3 * x) (T := T) (by simpa [hQ] using h3x)
        (by omega) (by omega) (by omega) hx0 hx1)
  by_contra hge
  have hle : Q.idxOf (3 * x) ≤ Q.idxOf (5 * x) := Nat.le_of_not_gt hge
  have hne : 5 * x ≠ 3 * x := by omega
  have hlt : Q.idxOf (3 * x) < Q.idxOf (5 * x) :=
    lt_of_le_of_ne hle fun heq => hne.symm (idxOf_eq_of_mem h3x h5 heq)
  have hcont := ((treeLt_safe_iff θ Q).mp hS).1
  have h5' : 2 * (3 * x) - x = 5 * x := by ring
  have h := hcont x (3 * x) hxmem h3x (by simpa [h5'] using h5) idxx_lt
    (by simpa [h5'] using hlt)
  have h7' : 3 * (3 * x) - 2 * x = 7 * x := by ring
  exact h7 (by simpa [h7'] using h.1)

/-- Forced escape for a true root-releasing tree-safe word beginning `(0,1,x)`
with `x ≥ 3` and `x ≡ 3 (mod 4)`. -/
theorem forced_escape_prefix (θ : ℕ → ℤ → Bool) (Q : List ℤ) (x : ℤ)
    (hx : (3 : ℤ) ≤ x) (hxmod : x % 4 = 3)
    (hS : Safe (treeLt θ) Q)
    (hpref : ∃ T : List ℤ, Q = 0 :: 1 :: x :: T)
    (hrel : ∀ a b : ℤ, a ∈ Q → b ∈ Q → Q.idxOf a < Q.idxOf b → 2 * b - a ∉ Q →
      3 * b - 2 * a ∉ Q → (b - a) % 2 = 1 → b % 2 = 0) :
    (3 * x ∈ Q) ∧
    (3 * x - 2 ∈ Q ∨ 7 * x ∈ Q ∨ (5 * x ∈ Q ∧ Q.idxOf (5 * x) < Q.idxOf (3 * x))) ∧
    (3 * x - 2 ∈ Q ∨ 5 * x ∈ Q ∨ 7 * x ∈ Q) := by
  have h3x : 3 * x ∈ Q := three_x_mem θ Q x hx hxmod hS hpref hrel
  have hesc :
      3 * x - 2 ∈ Q ∨ 7 * x ∈ Q ∨ (5 * x ∈ Q ∧ Q.idxOf (5 * x) < Q.idxOf (3 * x)) := by
    by_cases h32 : 3 * x - 2 ∈ Q
    · exact Or.inl h32
    · have h21 : 2 * x - 1 ∉ Q := two_x_sub_one_not_mem θ Q x hx hS hpref h32
      by_cases h7 : 7 * x ∈ Q
      · exact Or.inr (Or.inl h7)
      · by_cases h5 : 5 * x ∈ Q
        · exact Or.inr (Or.inr ⟨h5, five_before_three θ Q x hx hxmod hS hpref h3x h5 h7⟩)
        · exact (not_both_open θ Q x hx hxmod hS hpref h3x h21 h32 h5 h7).elim
  refine ⟨h3x, hesc, ?_⟩
  rcases hesc with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inr h)
  · exact Or.inr (Or.inl h.1)

private lemma not_dvd_two_of_ge_three {x : ℤ} (hx : (3 : ℤ) ≤ x) : ¬ x ∣ (2 : ℤ) := by
  intro hdv
  obtain ⟨k, hk⟩ := hdv
  have hnn : 0 ≤ x := le_trans (by decide : (0 : ℤ) ≤ 3) hx
  have habs : (x.natAbs : ℤ) = x := Int.natAbs_of_nonneg hnn
  have hge : 3 ≤ x.natAbs := by
    have : (3 : ℤ) ≤ x.natAbs := by
      simpa [habs] using hx
    exact_mod_cast this
  have hmul : x.natAbs * k.natAbs = 2 := by
    have := congrArg Int.natAbs hk
    rw [Int.natAbs_mul] at this
    have h2 : Int.natAbs (2 : ℤ) = 2 := rfl
    rw [h2] at this
    exact this.symm
  have hdiv : x.natAbs ∣ 2 := ⟨k.natAbs, hmul.symm⟩
  have : x.natAbs ≤ 2 := Nat.le_of_dvd (by decide : 0 < 2) hdiv
  omega

private lemma three_pow_ge_nine (n : ℕ) : (9 : ℤ) ≤ (3 : ℤ) ^ (n + 2) := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [pow_succ]
    nlinarith

private lemma three_pow_ne_five (n : ℕ) : (3 : ℤ) ^ n ≠ 5 := by
  intro h
  match n with
  | 0 => cases h
  | 1 => cases h
  | n + 2 =>
    have := three_pow_ge_nine n
    rw [h] at this
    linarith

private lemma three_pow_ne_seven (n : ℕ) : (3 : ℤ) ^ n ≠ 7 := by
  intro h
  match n with
  | 0 => cases h
  | 1 => cases h
  | n + 2 =>
    have := three_pow_ge_nine n
    rw [h] at this
    linarith

private lemma not_in_Sx_escape {x : ℤ} (hx : (3 : ℤ) ≤ x) :
    (∀ n : ℕ, 3 * x - 2 ≠ (3 : ℤ) ^ n ∧ 3 * x - 2 ≠ x * (3 : ℤ) ^ n) ∧
    (∀ n : ℕ, 5 * x ≠ (3 : ℤ) ^ n ∧ 5 * x ≠ x * (3 : ℤ) ^ n) ∧
    (∀ n : ℕ, 7 * x ≠ (3 : ℤ) ^ n ∧ 7 * x ≠ x * (3 : ℤ) ^ n) := by
  have hx0 : x ≠ 0 := by omega
  refine ⟨?_, ?_, ?_⟩
  · intro n
    refine ⟨?_, ?_⟩
    · intro h
      have hn0 : n ≠ 0 := by
        intro hn
        subst hn
        have : 3 * x - 2 = 1 := by simpa using h
        linarith
      have hmod : (3 * x - 2) % 3 = 1 := by
        have hx3 : (3 * x) % 3 = 0 := by
          rw [Int.mul_emod, Int.emod_self]
          simp
        omega
      have hpow : ((3 : ℤ) ^ n) % 3 = 0 := by
        obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hn0
        subst hm
        rw [pow_succ, Int.mul_emod, Int.emod_self]
        simp
      have : (3 * x - 2) % 3 = 0 := by rw [h, hpow]
      omega
    · intro h
      have : x ∣ 3 * x - 2 := by
        rw [h]
        exact dvd_mul_right _ _
      have : x ∣ (2 : ℤ) := by
        have h3x : x ∣ 3 * x := dvd_mul_left _ _
        have hsub := dvd_sub h3x this
        simpa using hsub
      exact not_dvd_two_of_ge_three hx this
  · intro n
    refine ⟨?_, ?_⟩
    · intro h
      have h5 : (5 : ℤ) ∣ (3 : ℤ) ^ n := ⟨x, by linarith⟩
      have h5N : (5 : ℕ) ∣ (3 : ℕ) ^ n := by exact_mod_cast h5
      have : 5 ∣ 3 := Nat.prime_five.dvd_of_dvd_pow h5N
      omega
    · intro h
      have h' : x * 5 = x * (3 : ℤ) ^ n := by simpa [mul_comm] using h
      have heq : (5 : ℤ) = (3 : ℤ) ^ n := Int.eq_of_mul_eq_mul_left hx0 h'
      exact three_pow_ne_five n heq.symm
  · intro n
    refine ⟨?_, ?_⟩
    · intro h
      have h7 : (7 : ℤ) ∣ (3 : ℤ) ^ n := ⟨x, by linarith⟩
      have h7N : (7 : ℕ) ∣ (3 : ℕ) ^ n := by exact_mod_cast h7
      have : 7 ∣ 3 := Nat.prime_seven.dvd_of_dvd_pow h7N
      omega
    · intro h
      have h' : x * 7 = x * (3 : ℤ) ^ n := by simpa [mul_comm] using h
      have heq : (7 : ℤ) = (3 : ℤ) ^ n := Int.eq_of_mul_eq_mul_left hx0 h'
      exact three_pow_ne_seven n heq.symm

/-- There is no θ-safe true root-releasing word beginning `(0,1,x)`, `x≥3`,
`x≡3 (mod 4)`, whose odd entries all lie on the two chains
`{3^n : n≥0} ∪ {x 3^n : n≥0}`. -/
theorem no_two_chain_only_prefix (θ : ℕ → ℤ → Bool) (Q : List ℤ) (x : ℤ)
    (hx : (3 : ℤ) ≤ x) (hxmod : x % 4 = 3)
    (hS : Safe (treeLt θ) Q)
    (hpref : ∃ T : List ℤ, Q = 0 :: 1 :: x :: T)
    (hrel : ∀ a b : ℤ, a ∈ Q → b ∈ Q → Q.idxOf a < Q.idxOf b → 2 * b - a ∉ Q →
      3 * b - 2 * a ∉ Q → (b - a) % 2 = 1 → b % 2 = 0)
    (hodd : ∀ z ∈ Q, z % 2 = 1 →
      ∃ n : ℕ, z = (3 : ℤ) ^ n ∨ z = x * (3 : ℤ) ^ n) :
    False := by
  have hesc := (forced_escape_prefix θ Q x hx hxmod hS hpref hrel).2.2
  have hxodd : x % 2 = 1 := x_odd hxmod
  have h32odd : (3 * x - 2) % 2 = 1 := by omega
  have h5odd : (5 * x) % 2 = 1 := by omega
  have h7odd : (7 * x) % 2 = 1 := by omega
  have hSx := not_in_Sx_escape (x := x) hx
  rcases hesc with h32 | h5 | h7
  · obtain ⟨n, hn⟩ := hodd (3 * x - 2) h32 h32odd
    rcases hn with h | h
    · exact (hSx.1 n).1 h
    · exact (hSx.1 n).2 h
  · obtain ⟨n, hn⟩ := hodd (5 * x) h5 h5odd
    rcases hn with h | h
    · exact (hSx.2.1 n).1 h
    · exact (hSx.2.1 n).2 h
  · obtain ⟨n, hn⟩ := hodd (7 * x) h7 h7odd
    rcases hn with h | h
    · exact (hSx.2.2 n).1 h
    · exact (hSx.2.2 n).2 h

end Erdos195

theorem solution (θ : ℕ → ℤ → Bool) (Q : List ℤ) (x : ℤ)
    (hx : (3 : ℤ) ≤ x) (hxmod : x % 4 = 3)
    (hS : Erdos195.Safe (Erdos195.treeLt θ) Q)
    (hpref : ∃ T : List ℤ, Q = 0 :: 1 :: x :: T)
    (hrel : ∀ a b : ℤ, a ∈ Q → b ∈ Q → Q.idxOf a < Q.idxOf b → 2 * b - a ∉ Q →
      3 * b - 2 * a ∉ Q → (b - a) % 2 = 1 → b % 2 = 0) :
    (3 * x ∈ Q) ∧
    (3 * x - 2 ∈ Q ∨ 7 * x ∈ Q ∨ (5 * x ∈ Q ∧ Q.idxOf (5 * x) < Q.idxOf (3 * x))) ∧
    (3 * x - 2 ∈ Q ∨ 5 * x ∈ Q ∨ 7 * x ∈ Q) :=
  Erdos195.forced_escape_prefix θ Q x hx hxmod hS hpref hrel
