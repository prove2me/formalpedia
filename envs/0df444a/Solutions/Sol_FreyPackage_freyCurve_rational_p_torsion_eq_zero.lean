-- Prove2me | solution 1 for FreyPackage.freyCurve_rational_p_torsion_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/2708e918-b712-5386-8d1b-6bffcae16151

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FreyPackage_freyCurve_rational_p_torsion_eq_zero

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

namespace S04

local notation "v" => padicValRat 2

private def _root_.S04.I (n : ℤ) (q : ℚ) : Prop := q = 0 ∨ n ≤ v q

p2m_export "S04" "I"
lemma I_zero (n : ℤ) : I n 0 := Or.inl rfl

lemma I_of_le {n m : ℤ} {q : ℚ} (h : I m q) (hnm : n ≤ m) : I n q := by
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (le_trans hnm h)

lemma I_neg {n : ℤ} {q : ℚ} (h : I n q) : I n (-q) := by
  rcases h with h | h
  · exact Or.inl (by rw [h, _root_.neg_zero])
  · exact Or.inr (by rwa [padicValRat.neg])

lemma I_add {n : ℤ} {q r : ℚ} (hq : I n q) (hr : I n r) : I n (q + r) := by
  by_cases hqr : q + r = 0
  · exact Or.inl hqr
  rcases hq with hq | hq
  · subst hq; simpa using hr
  rcases hr with hr | hr
  · subst hr; simp only [add_zero]; exact Or.inr hq
  exact Or.inr (le_trans (le_min hq hr) (padicValRat.min_le_padicValRat_add hqr))

lemma I_sub {n : ℤ} {q r : ℚ} (hq : I n q) (hr : I n r) : I n (q - r) := by
  rw [sub_eq_add_neg]; exact I_add hq (I_neg hr)

lemma I_mul {n m : ℤ} {q r : ℚ} (hq : I n q) (hr : I m r) : I (n + m) (q * r) := by
  rcases hq with hq | hq
  · exact Or.inl (by rw [hq, zero_mul])
  rcases hr with hr | hr
  · exact Or.inl (by rw [hr, mul_zero])
  by_cases hq0 : q = 0
  · exact Or.inl (by rw [hq0, zero_mul])
  by_cases hr0 : r = 0
  · exact Or.inl (by rw [hr0, mul_zero])
  exact Or.inr (by rw [padicValRat.mul hq0 hr0]; omega)

lemma I_pow_two {n : ℤ} {q : ℚ} (hq : I n q) : I (n + n) (q ^ 2) := by
  rw [pow_two]; exact I_mul hq hq

lemma I_int (z : ℤ) : I 0 (z : ℚ) := by
  by_cases hz : (z : ℚ) = 0
  · exact Or.inl hz
  · exact Or.inr (by rw [padicValRat.of_int]; exact_mod_cast Nat.zero_le _)

lemma I_nat (k : ℕ) : I 0 (k : ℚ) := by
  have := I_int (k : ℤ); simpa using this

lemma I_two : I 1 (2 : ℚ) := by
  right; rw [show (2 : ℚ) = ((2 : ℕ) : ℚ) by norm_num, padicValRat.of_nat]; simp

lemma v_two : v (2 : ℚ) = 1 := by
  rw [show (2 : ℚ) = ((2 : ℕ) : ℚ) by norm_num, padicValRat.self (by norm_num)]

def E (n : ℤ) (q : ℚ) : Prop := q ≠ 0 ∧ v q = n

lemma E.I {n : ℤ} {q : ℚ} (h : E n q) : I n q := Or.inr h.2.ge

lemma E_mul {n m : ℤ} {q r : ℚ} (hq : E n q) (hr : E m r) : E (n + m) (q * r) :=
  ⟨mul_ne_zero hq.1 hr.1, by rw [padicValRat.mul hq.1 hr.1, hq.2, hr.2]⟩

lemma E_pow_two {n : ℤ} {q : ℚ} (hq : E n q) : E (n + n) (q ^ 2) := by
  rw [pow_two]; exact E_mul hq hq

lemma E_div {n m : ℤ} {q r : ℚ} (hq : E n q) (hr : E m r) : E (n - m) (q / r) :=
  ⟨div_ne_zero hq.1 hr.1, by rw [padicValRat.div hq.1 hr.1, hq.2, hr.2]⟩

lemma E_neg {n : ℤ} {q : ℚ} (hq : E n q) : E n (-q) :=
  ⟨neg_ne_zero.mpr hq.1, by rw [padicValRat.neg, hq.2]⟩

lemma E_add_I {n m : ℤ} {q r : ℚ} (hq : E n q) (hr : I m r) (hnm : n < m) : E n (q + r) := by
  rcases hr with hr | hr
  · subst hr; simpa using hq
  by_cases hr0 : r = 0
  · subst hr0; simpa using hq
  have hlt : v q < v r := by rw [hq.2]; omega
  have hqr : q + r ≠ 0 := by
    intro h
    have : r = -q := by linear_combination h
    rw [this, padicValRat.neg] at hlt
    exact lt_irrefl _ hlt
  exact ⟨hqr, by rw [padicValRat.add_eq_of_lt hqr hq.1 hr0 hlt, hq.2]⟩

lemma I_add_E {n m : ℤ} {q r : ℚ} (hq : I m q) (hr : E n r) (hnm : n < m) : E n (q + r) := by
  rw [add_comm]; exact E_add_I hr hq hnm

lemma E_sub_I {n m : ℤ} {q r : ℚ} (hq : E n q) (hr : I m r) (hnm : n < m) : E n (q - r) := by
  rw [sub_eq_add_neg]; exact E_add_I hq (I_neg hr) hnm

lemma I_sub_E {n m : ℤ} {q r : ℚ} (hq : I m q) (hr : E n r) (hnm : n < m) : E n (q - r) := by
  rw [sub_eq_add_neg]; exact I_add_E hq (E_neg hr) hnm

lemma E_I_absurd {n m : ℤ} {q : ℚ} (hq : E n q) (hq' : I m q) (hnm : n < m) : False := by
  rcases hq' with h | h
  · exact hq.1 h
  · rw [hq.2] at h; omega

lemma I_one_sub_one_of_unit {q : ℚ} (hq : E 0 q) : I 1 (q - 1) := by
  obtain ⟨hq0, hv⟩ := hq
  have hnum : q.num ≠ 0 := Rat.num_ne_zero.mpr hq0
  have hden : q.den ≠ 0 := q.den_ne_zero
  have hdef : v q = padicValInt 2 q.num - padicValNat 2 q.den := padicValRat_def 2 q
  have hcop : Nat.Coprime q.num.natAbs q.den := q.reduced

  have hn2 : ¬ (2 : ℤ) ∣ q.num := by
    intro h2
    have hd2 : ¬ 2 ∣ q.den := by
      intro hd
      have h2' : 2 ∣ q.num.natAbs := by
        rcases h2 with ⟨k, hk⟩; exact ⟨k.natAbs, by rw [hk, Int.natAbs_mul]; rfl⟩
      have := Nat.eq_one_of_dvd_coprimes hcop h2' hd
      omega
    have hvd : padicValNat 2 q.den = 0 := padicValNat.eq_zero_of_not_dvd hd2
    have hvn : 1 ≤ padicValInt 2 q.num := by
      have := (padicValInt_dvd_iff 1 q.num).mp (by simp at h2 ⊢; exact h2)
      rcases this with h | h
      · exact absurd h hnum
      · exact h
    rw [hvd] at hdef; omega
  have hvn : padicValInt 2 q.num = 0 := padicValInt.eq_zero_of_not_dvd hn2
  have hvd : padicValNat 2 q.den = 0 := by rw [hvn] at hdef; omega
  have hd2 : ¬ 2 ∣ q.den := by
    intro hd
    have := one_le_padicValNat_of_dvd hden hd
    omega

  have hd0 : (q.den : ℚ) ≠ 0 := by exact_mod_cast hden
  have hq_eq : q - 1 = ((q.num - q.den : ℤ) : ℚ) / (q.den : ℚ) := by
    push_cast
    rw [sub_div, div_self hd0, Rat.num_div_den q]
  by_cases hnd : (q.num - q.den : ℤ) = 0
  · left; rw [hq_eq, hnd]; simp
  right
  have heven : (2 : ℤ) ∣ q.num - q.den := by
    have hn_odd : Odd q.num := Int.not_even_iff_odd.mp (fun h => hn2 (even_iff_two_dvd.mp h))
    have hd_odd : Odd (q.den : ℤ) := by
      have : Odd q.den := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hd2)
      exact (Int.odd_coe_nat _).mpr this
    exact even_iff_two_dvd.mp (Odd.sub_odd hn_odd hd_odd)
  have hnd0 : ((q.num - q.den : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hnd
  rw [hq_eq, padicValRat.div hnd0 hd0, padicValRat.of_int, padicValRat.of_nat, hvd]
  have h1 : 1 ≤ padicValInt 2 (q.num - q.den) := by
    rcases (padicValInt_dvd_iff 1 (q.num - q.den)).mp (by simp at heven ⊢; exact heven) with h | h
    · exact absurd h hnd
    · exact h
  push_cast
  omega

lemma unit_add_I {q r : ℚ} (hq : E 0 q) (hr : I 1 r) : E 0 (q + r) := E_add_I hq hr (by norm_num)

lemma I_one_add_of_units {q r : ℚ} (hq : E 0 q) (hr : E 0 r) : I 1 (q + r) := by
  have h1 := I_one_sub_one_of_unit hq
  have h2 := I_one_sub_one_of_unit hr
  have : q + r = (q - 1) + (r - 1) + 2 := by ring
  rw [this]
  exact I_add (I_add h1 h2) I_two

lemma I_one_sub_of_units {q r : ℚ} (hq : E 0 q) (hr : E 0 r) : I 1 (q - r) := by
  have h1 := I_one_sub_one_of_unit hq
  have h2 := I_one_sub_one_of_unit hr
  have : q - r = (q - 1) - (r - 1) := by ring
  rw [this]
  exact I_sub h1 h2

lemma I_one_mul_add_one {q : ℚ} (hq : I 0 q) : I 1 (q * (q + 1)) := by
  by_cases hq0 : q = 0
  · exact Or.inl (by rw [hq0, zero_mul])
  rcases hq with h | h
  · exact absurd h hq0
  by_cases hv : v q = 0
  ·
    have hu : E 0 q := ⟨hq0, hv⟩
    have h1 : I 1 (q + 1) := by
      have : q + 1 = (q - 1) + 2 := by ring
      rw [this]; exact I_add (I_one_sub_one_of_unit hu) I_two
    have := I_mul (Or.inr h : I 0 q) h1
    simpa using this
  · have hq1 : I 1 q := Or.inr (by omega)
    have h1 : I 0 (q + 1) := I_add (Or.inr h) (by exact_mod_cast I_int 1)
    have := I_mul hq1 h1
    simpa using this

lemma I_div_E {n m : ℤ} {q r : ℚ} (hq : I n q) (hr : E m r) : I (n - m) (q / r) := by
  rcases hq with hq | hq
  · exact Or.inl (by rw [hq, zero_div])
  by_cases hq0 : q = 0
  · exact Or.inl (by rw [hq0, zero_div])
  exact Or.inr (by rw [padicValRat.div hq0 hr.1, hr.2]; omega)

lemma E.ne {n : ℤ} {q : ℚ} (h : E n q) : q ≠ 0 := h.1

lemma E_of_v {q : ℚ} (hq : q ≠ 0) : E (v q) q := ⟨hq, rfl⟩

lemma E_three : E 0 (3 : ℚ) := by
  refine ⟨by norm_num, ?_⟩
  rw [show (3 : ℚ) = ((3 : ℕ) : ℚ) by norm_num, padicValRat.of_nat]
  simp [padicValNat.eq_zero_of_not_dvd (show ¬ 2 ∣ 3 by omega)]

lemma E_two : E 1 (2 : ℚ) := ⟨by norm_num, v_two⟩

lemma E_four : E 2 (4 : ℚ) := by
  have := E_mul E_two E_two; norm_num at this; exact this

lemma E_sixteen : E 4 (16 : ℚ) := by
  have := E_mul E_four E_four; norm_num at this; exact this

section Frey

variable (P : FreyPackage)

lemma frey_a₁ : (P.freyCurve⁄ℚ).a₁ = 1 := by simp [FreyPackage.freyCurve]
lemma frey_a₃ : (P.freyCurve⁄ℚ).a₃ = 0 := by simp [FreyPackage.freyCurve]
lemma frey_a₆ : (P.freyCurve⁄ℚ).a₆ = 0 := by simp [FreyPackage.freyCurve]
lemma frey_a₂ : (P.freyCurve⁄ℚ).a₂ = ((P.b : ℚ) ^ P.p - 1 - (P.a : ℚ) ^ P.p) / 4 := by
  simp [FreyPackage.freyCurve]
lemma frey_a₄ : (P.freyCurve⁄ℚ).a₄ = -((P.a : ℚ) ^ P.p) * (P.b : ℚ) ^ P.p / 16 := by
  simp [FreyPackage.freyCurve]

lemma frey_negY (x y : ℚ) : (P.freyCurve⁄ℚ).negY x y = -y - x := by
  simp [negY, FreyPackage.freyCurve]

lemma frey_eqn {x y : ℚ} (h : (P.freyCurve⁄ℚ).Nonsingular x y) :
    y ^ 2 + x * y = x ^ 3 + (P.freyCurve⁄ℚ).a₂ * x ^ 2 + (P.freyCurve⁄ℚ).a₄ * x := by
  have he := (equation_iff x y).mp h.left
  rw [frey_a₁, frey_a₃, frey_a₆] at he
  linear_combination he

lemma frey_a_mod_four : P.a % 4 = 3 := by
  have h := P.ha4
  have : (P.a : ZMod 4) = ((3 : ℤ) : ZMod 4) := by rw [h]; rfl
  rw [ZMod.intCast_eq_intCast_iff'] at this
  norm_num at this
  exact this

lemma frey_two_not_dvd_a : ¬ (2 : ℤ) ∣ P.a := by
  have := frey_a_mod_four P; omega

lemma frey_two_dvd_b : (2 : ℤ) ∣ P.b := by
  have h := P.hb2
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd P.b 2).mp h

lemma frey_Ea : E 0 (P.a : ℚ) := by
  refine ⟨by exact_mod_cast P.ha0, ?_⟩
  rw [padicValRat.of_int, padicValInt.eq_zero_of_not_dvd (frey_two_not_dvd_a P)]
  rfl

lemma frey_vb_pos : 1 ≤ padicValInt 2 P.b := by
  rcases (padicValInt_dvd_iff 1 P.b).mp (by have h__af := frey_two_dvd_b P; simp at h__af ⊢; exact h__af) with h | h
  · exact absurd h P.hb0
  · exact h

lemma frey_Eb : E (padicValInt 2 P.b : ℤ) (P.b : ℚ) :=
  ⟨by exact_mod_cast P.hb0, by rw [padicValRat.of_int]⟩

lemma E_pow {n : ℤ} {q : ℚ} (hq : E n q) (k : ℕ) : E (k * n) (q ^ k) :=
  ⟨pow_ne_zero _ hq.1, by rw [padicValRat.pow _, hq.2]⟩

lemma frey_EA : E 0 ((P.a : ℚ) ^ P.p) := by
  have := E_pow (frey_Ea P) P.p; simpa using this

lemma frey_EB : E ((P.p : ℤ) * (padicValInt 2 P.b : ℤ)) ((P.b : ℚ) ^ P.p) :=
  E_pow (frey_Eb P) P.p

lemma frey_beta_ge : (5 : ℤ) ≤ (P.p : ℤ) * (padicValInt 2 P.b : ℤ) := by
  have h1 := frey_vb_pos P
  have h5 := P.hp5
  calc (5 : ℤ) = 5 * 1 := by norm_num
    _ ≤ (P.p : ℤ) * (padicValInt 2 P.b : ℤ) :=
      mul_le_mul (by exact_mod_cast h5) (by exact_mod_cast h1) (by norm_num) (by positivity)

lemma frey_four_dvd : (4 : ℤ) ∣ P.b ^ P.p - 1 - P.a ^ P.p := by
  have hb : ((P.b ^ P.p : ℤ) : ZMod 4) = 0 := by
    obtain ⟨k, hk⟩ := frey_two_dvd_b P
    have hp2 : 2 ≤ P.p := le_trans (by norm_num) P.hp5
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hp2
    rw [hk, hm]
    push_cast
    rw [mul_pow, pow_add]
    have : ((2 : ZMod 4)) ^ 2 = 0 := by decide
    rw [this]; ring
  have ha : ((P.a ^ P.p : ℤ) : ZMod 4) = 3 := by
    push_cast
    rw [P.ha4]
    obtain ⟨m, hm⟩ := P.hp_odd
    rw [hm, pow_add, pow_mul]
    have : ((3 : ZMod 4)) ^ 2 = 1 := by decide
    rw [this]; ring
  have : ((P.b ^ P.p - 1 - P.a ^ P.p : ℤ) : ZMod 4) = 0 := by
    push_cast at hb ha ⊢
    rw [hb, ha]; decide
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mp this

lemma frey_I_a₂ : I 0 (P.freyCurve⁄ℚ).a₂ := by
  obtain ⟨k, hk⟩ := frey_four_dvd P
  have : (P.freyCurve⁄ℚ).a₂ = (k : ℚ) := by
    rw [frey_a₂]
    have hk' : ((P.b : ℚ) ^ P.p - 1 - (P.a : ℚ) ^ P.p) = 4 * (k : ℚ) := by exact_mod_cast hk
    rw [hk']; ring
  rw [this]; exact I_int k

lemma frey_E_a₄ : E ((P.p : ℤ) * (padicValInt 2 P.b : ℤ) - 4) (P.freyCurve⁄ℚ).a₄ := by
  rw [frey_a₄]
  have h := E_div (E_mul (E_neg (frey_EA P)) (frey_EB P)) E_sixteen
  simpa using h

lemma frey_gamma_ge : (1 : ℤ) ≤ (P.p : ℤ) * (padicValInt 2 P.b : ℤ) - 4 := by
  have := frey_beta_ge P; omega

lemma frey_I_a₄ : I 1 (P.freyCurve⁄ℚ).a₄ := I_of_le (frey_E_a₄ P).I (frey_gamma_ge P)

end Frey

section Points

variable (P : FreyPackage)

def xc : (P.freyCurve⁄ℚ).Point → ℚ
  | .zero => 0
  | .some x _ _ => x

@[scoped simp] lemma xc_zero : xc P 0 = 0 := rfl
@[scoped simp] lemma xc_zero' : xc P .zero = 0 := rfl
@[scoped simp] lemma xc_some {x y : ℚ} (h : (P.freyCurve⁄ℚ).Nonsingular x y) :
    xc P (.some x y h) = x := rfl

variable {P}

lemma frey_I_y {x y : ℚ} (h : (P.freyCurve⁄ℚ).Nonsingular x y) (hx : I 0 x) : I 0 y := by
  by_cases hy0 : y = 0
  · exact Or.inl hy0
  by_contra hy
  have hf : v y < 0 := by
    simp only [I, not_or, not_le] at hy; exact hy.2
  have heq := frey_eqn P h

  have hR : I 0 (x ^ 3 + (P.freyCurve⁄ℚ).a₂ * x ^ 2 + (P.freyCurve⁄ℚ).a₄ * x) := by
    have h3 : I 0 (x ^ 3) := by
      have := I_mul hx (I_pow_two hx); rw [← pow_succ'] at this; simpa using this
    have h2 : I 0 ((P.freyCurve⁄ℚ).a₂ * x ^ 2) := by
      have := I_mul (frey_I_a₂ P) (I_pow_two hx); simpa using this
    have h1 : I 0 ((P.freyCurve⁄ℚ).a₄ * x) := by
      have := I_mul (I_of_le (frey_I_a₄ P) (by norm_num : (0:ℤ) ≤ 1)) hx; simpa using this
    exact I_add (I_add h3 h2) h1

  have hEy : E (v y) y := E_of_v hy0
  have hL : E (v y + v y) (y ^ 2 + x * y) := by
    have h1 : E (v y + v y) (y ^ 2) := E_pow_two hEy
    have h2 : I (0 + v y) (x * y) := I_mul hx hEy.I
    exact E_add_I h1 h2 (by omega)
  rw [heq] at hL
  exact E_I_absurd hL hR (by omega)

lemma frey_neg_val {x y : ℚ} (h : (P.freyCurve⁄ℚ).Nonsingular x y) {e : ℤ} (hx : E e x)
    (he : e < 0) : y ≠ 0 ∧ v y < e ∧ 2 * v y = 3 * e := by
  have heq := frey_eqn P h

  have hR : E (3 * e) (x ^ 3 + (P.freyCurve⁄ℚ).a₂ * x ^ 2 + (P.freyCurve⁄ℚ).a₄ * x) := by
    have h3 : E (3 * e) (x ^ 3) := by have := E_pow hx 3; simpa using this
    have h2 : I (0 + (e + e)) ((P.freyCurve⁄ℚ).a₂ * x ^ 2) := I_mul (frey_I_a₂ P) (I_pow_two hx.I)
    have h1 : I (1 + e) ((P.freyCurve⁄ℚ).a₄ * x) := I_mul (frey_I_a₄ P) hx.I
    exact E_add_I (E_add_I h3 h2 (by omega)) h1 (by omega)
  by_cases hy0 : y = 0
  · subst hy0
    have : E (3 * e) (0 : ℚ) := by
      have h0 : (0:ℚ) ^ 2 + x * 0 = 0 := by ring
      rw [← h0, heq]; exact hR
    exact absurd rfl this.1
  have hEy : E (v y) y := E_of_v hy0
  refine ⟨hy0, ?_⟩
  rcases lt_trichotomy (v y) e with hlt | heq' | hgt
  ·
    have hL : E (v y + v y) (y ^ 2 + x * y) :=
      E_add_I (E_pow_two hEy) (I_mul hx.I hEy.I) (by omega)
    rw [heq] at hL
    have := hL.2.symm.trans hR.2
    exact ⟨hlt, by omega⟩
  ·
    exfalso
    have hL : I (e + e) (y ^ 2 + x * y) := by
      have hy' : I e y := Or.inr heq'.ge
      exact I_add (I_pow_two hy') (I_mul hx.I hy')
    rw [heq] at hL
    exact E_I_absurd hR hL (by omega)
  ·
    exfalso
    have hL : E (v y + e) (y ^ 2 + x * y) := by
      have : y ^ 2 + x * y = y * (y + x) := by ring
      rw [this]
      exact E_mul hEy (I_add_E hEy.I hx hgt)
    rw [heq] at hL
    have := hL.2.symm.trans hR.2
    omega

lemma frey_double_neg {x y : ℚ} (h : (P.freyCurve⁄ℚ).Nonsingular x y) {e : ℤ} (hx : E e x)
    (he : e < 0) (hy : y ≠ (P.freyCurve⁄ℚ).negY x y) :
    (P.freyCurve⁄ℚ).addX x x ((P.freyCurve⁄ℚ).slope x x y y) ≠ 0 ∧
    v ((P.freyCurve⁄ℚ).addX x x ((P.freyCurve⁄ℚ).slope x x y y)) ≤ e - 2 := by
  obtain ⟨hy0, hylt, h23⟩ := frey_neg_val h hx he
  have hEy : E (v y) y := E_of_v hy0
  set f := v y with hf

  have hD : y - (P.freyCurve⁄ℚ).negY x y = x + 2 * y := by rw [frey_negY]; ring
  have hD0 : x + 2 * y ≠ 0 := by rw [← hD]; exact sub_ne_zero.mpr hy
  have hDv : 1 + f ≤ v (x + 2 * y) := by
    have h2y : E (1 + f) (2 * y) := E_mul E_two hEy
    rcases lt_or_ge (1 + f) e with hlt | hge
    · exact (I_add_E hx.I h2y hlt).2.ge
    ·
      have hfe : 1 + f = e := by omega
      have hI : I (1 + f) (x + 2 * y) := I_add (by rw [hfe]; exact hx.I) h2y.I
      rcases hI with h0 | h0
      · exact absurd h0 hD0
      · exact h0

  have hN : E (e + e) (3 * x ^ 2 + 2 * (P.freyCurve⁄ℚ).a₂ * x + (P.freyCurve⁄ℚ).a₄ -
      (P.freyCurve⁄ℚ).a₁ * y) := by
    rw [frey_a₁, one_mul]
    have h1 : E (0 + (e + e)) (3 * x ^ 2) := E_mul E_three (E_pow_two hx)
    have h2 : I (1 + 0 + e) (2 * (P.freyCurve⁄ℚ).a₂ * x) := I_mul (I_mul I_two (frey_I_a₂ P)) hx.I
    have h3 : I 1 (P.freyCurve⁄ℚ).a₄ := frey_I_a₄ P
    have h4 : I f y := hEy.I
    have := E_sub_I (E_add_I (E_add_I h1 h2 (by omega)) h3 (by omega)) h4 (by omega)
    simpa using this

  have hslope : (P.freyCurve⁄ℚ).slope x x y y =
      (3 * x ^ 2 + 2 * (P.freyCurve⁄ℚ).a₂ * x + (P.freyCurve⁄ℚ).a₄ - (P.freyCurve⁄ℚ).a₁ * y) /
        (x + 2 * y) := by
    rw [slope_of_Y_ne rfl hy, hD]
  set ℓ := (P.freyCurve⁄ℚ).slope x x y y with hℓ
  have hEℓ : E (e + e - v (x + 2 * y)) ℓ := by
    rw [hslope]; exact E_div hN (E_of_v hD0)
  set m := e + e - v (x + 2 * y) with hm
  have hm2 : m + m ≤ e - 2 := by omega
  have hmneg : m < 0 := by omega

  have hX : E (m + m) ((P.freyCurve⁄ℚ).addX x x ℓ) := by
    simp only [addX, frey_a₁, one_mul]
    have h1 : E (m + m) (ℓ ^ 2) := E_pow_two hEℓ
    have h2 : I m ℓ := hEℓ.I
    exact E_sub_I (E_sub_I (E_sub_I (E_add_I h1 h2 (by omega)) (frey_I_a₂ P) (by omega))
      hx.I (by omega)) hx.I (by omega)
  exact ⟨hX.1, by rw [hX.2]; exact hm2⟩

end Points

section Orbit

variable {P : FreyPackage}

theorem frey_I_xc_nsmul (Q : (P.freyCurve⁄ℚ).Point) (hQ : addOrderOf Q = P.p) (k : ℕ) :
    I 0 (xc P (k • Q)) := by
  classical
  by_contra hbad
  have hp5 := P.hp5
  have hpp := P.pp
  set f : ℕ → ℤ := fun k => v (xc P (k • Q)) with hf
  obtain ⟨k₀, -, hmin⟩ := (Finset.range P.p).exists_min_image f
    ⟨0, Finset.mem_range.mpr P.hppos⟩

  have hmodk : (k % P.p) • Q = k • Q := by rw [← hQ]; exact mod_addOrderOf_nsmul Q k
  have hbad' : f (k % P.p) < 0 := by
    simp only [I, not_or, not_le] at hbad
    show v (xc P ((k % P.p) • Q)) < 0
    rw [hmodk]; exact hbad.2
  have hk0neg : f k₀ < 0 :=
    lt_of_le_of_lt (hmin _ (Finset.mem_range.mpr (Nat.mod_lt _ P.hppos))) hbad'

  rcases hR : k₀ • Q with _ | ⟨x, y, h⟩
  · have : f k₀ = 0 := by
      show v (xc P (k₀ • Q)) = 0
      rw [hR, xc_zero', padicValRat.zero]
    omega
  have hfx : f k₀ = v x := by
    show v (xc P (k₀ • Q)) = v x
    rw [hR, xc_some]
  have hx : E (f k₀) x := by
    refine ⟨?_, hfx.symm⟩
    intro hx0
    rw [hfx, hx0, padicValRat.zero] at hk0neg
    exact lt_irrefl _ hk0neg

  have hk₀p : ¬ P.p ∣ k₀ := by
    intro hdvd
    have h0 : k₀ • Q = 0 := by
      rw [← hQ] at hdvd; exact addOrderOf_dvd_iff_nsmul_eq_zero.mp hdvd
    rw [hR] at h0; exact (some_ne_zero h) h0
  have h2ne : (k₀ * 2) • Q ≠ 0 := by
    intro h0
    have hdvd : P.p ∣ k₀ * 2 := by rw [← hQ]; exact addOrderOf_dvd_iff_nsmul_eq_zero.mpr h0
    rcases (Nat.Prime.dvd_mul hpp).mp hdvd with h1 | h1
    · exact hk₀p h1
    · have := Nat.le_of_dvd (by norm_num) h1; omega
  have hy : y ≠ (P.freyCurve⁄ℚ).negY x y := by
    intro hyy
    apply h2ne
    rw [mul_nsmul, hR, two_nsmul, add_self_of_Y_eq hyy]
  obtain ⟨-, hv3⟩ := frey_double_neg h hx hk0neg hy

  have hsum : (k₀ * 2) • Q = .some _ _ (nonsingular_add h h fun hxy => hy hxy.right) := by
    rw [mul_nsmul, hR, two_nsmul, add_self_of_Y_ne hy]
  have hmod2 : ((k₀ * 2) % P.p) • Q = (k₀ * 2) • Q := by
    rw [← hQ]; exact mod_addOrderOf_nsmul Q (k₀ * 2)
  have hf2 : f ((k₀ * 2) % P.p) =
      v ((P.freyCurve⁄ℚ).addX x x ((P.freyCurve⁄ℚ).slope x x y y)) := by
    show v (xc P (((k₀ * 2) % P.p) • Q)) = _
    rw [hmod2, hsum, xc_some]
  have hle := hmin ((k₀ * 2) % P.p) (Finset.mem_range.mpr (Nat.mod_lt _ P.hppos))
  omega

lemma frey_x_ne_zero_of_order (Q : (P.freyCurve⁄ℚ).Point) (hQ : addOrderOf Q = P.p)
    {x y : ℚ} {h : (P.freyCurve⁄ℚ).Nonsingular x y} (hxy : Q = .some x y h) : x ≠ 0 := by
  intro hx0
  have hp5 := P.hp5
  have heq := frey_eqn P h
  rw [hx0] at heq
  have hy0 : y = 0 := by
    have : y ^ 2 = 0 := by linear_combination heq
    exact pow_eq_zero_iff (by norm_num) |>.mp this
  have hneg : y = (P.freyCurve⁄ℚ).negY x y := by rw [frey_negY, hx0, hy0]; norm_num
  have h2 : (2:ℕ) • Q = 0 := by rw [two_nsmul, hxy, add_self_of_Y_eq hneg]
  have hdvd : P.p ∣ 2 := by rw [← hQ]; exact addOrderOf_dvd_iff_nsmul_eq_zero.mpr h2
  have := Nat.le_of_dvd (by norm_num) hdvd
  omega

theorem frey_deep_of_order (Q : (P.freyCurve⁄ℚ).Point) (hQ : addOrderOf Q = P.p) {x y : ℚ}
    {h : (P.freyCurve⁄ℚ).Nonsingular x y} (hxy : Q = .some x y h) : 1 ≤ v x := by
  have hp5 := P.hp5
  have hx0 : x ≠ 0 := frey_x_ne_zero_of_order Q hQ hxy
  have hI1 : I 0 x := by
    have := frey_I_xc_nsmul Q hQ 1; rwa [one_nsmul, hxy, xc_some] at this
  by_contra hlt
  have hEx : E 0 x := by
    refine ⟨hx0, ?_⟩
    rcases hI1 with h0 | h0
    · exact absurd h0 hx0
    · omega
  have hIy : I 0 y := frey_I_y h hI1
  have heq := frey_eqn P h
  by_cases hA2 : I 1 (P.freyCurve⁄ℚ).a₂
  ·
    have hL : I 1 (y ^ 2 + x * y) := by
      by_cases hyu : E 0 y
      · have hfac : y ^ 2 + x * y = y * (y + x) := by ring
        rw [hfac]
        have := I_mul hyu.I (I_one_add_of_units hyu hEx)
        simpa using this
      · have hy1 : I 1 y := by
          by_cases hy0 : y = 0
          · exact Or.inl hy0
          · rcases hIy with h0 | h0
            · exact absurd h0 hy0
            · have : v y ≠ 0 := fun hv => hyu ⟨hy0, hv⟩
              exact Or.inr (by omega)
        have h1 : I (1 + 1) (y ^ 2) := I_pow_two hy1
        have h2 : I (0 + 1) (x * y) := I_mul hEx.I hy1
        exact I_add (I_of_le h1 (by norm_num)) (I_of_le h2 (by norm_num))
    have hR : E 0 (x ^ 3 + (P.freyCurve⁄ℚ).a₂ * x ^ 2 + (P.freyCurve⁄ℚ).a₄ * x) := by
      have h3 : E 0 (x ^ 3) := by have := E_pow hEx 3; simpa using this
      have h2 : I (1 + (0 + 0)) ((P.freyCurve⁄ℚ).a₂ * x ^ 2) := I_mul hA2 (I_pow_two hEx.I)
      have h1 : I (1 + 0) ((P.freyCurve⁄ℚ).a₄ * x) := I_mul (frey_I_a₄ P) hEx.I
      exact E_add_I (E_add_I h3 h2 (by norm_num)) h1 (by norm_num)
    rw [heq] at hL
    exact E_I_absurd hR hL (by norm_num)
  ·
    have hEA2 : E 0 (P.freyCurve⁄ℚ).a₂ := by
      refine ⟨fun h00 => hA2 (Or.inl h00), ?_⟩
      rcases frey_I_a₂ P with h0 | h0
      · exact absurd (Or.inl h0) hA2
      · by_contra hv; exact hA2 (Or.inr (by omega))

    have hD : y - (P.freyCurve⁄ℚ).negY x y = x + 2 * y := by rw [frey_negY]; ring
    have h2y : I 1 (2 * y) := by have := I_mul I_two hIy; simpa using this
    have h2x : I 1 (2 * x) := by have := I_mul I_two hEx.I; simpa using this
    have hED : E 0 (x + 2 * y) := E_add_I hEx h2y (by norm_num)
    have hy : y ≠ (P.freyCurve⁄ℚ).negY x y := by
      intro hyy; apply hED.1; rw [← hD]; exact sub_eq_zero.mpr hyy
    have hN : I 0 (3 * x ^ 2 + 2 * (P.freyCurve⁄ℚ).a₂ * x + (P.freyCurve⁄ℚ).a₄ -
        (P.freyCurve⁄ℚ).a₁ * y) := by
      rw [frey_a₁, one_mul]
      have h1 : I (0 + (0 + 0)) (3 * x ^ 2) := I_mul E_three.I (I_pow_two hEx.I)
      have h2 : I (1 + 0 + 0) (2 * (P.freyCurve⁄ℚ).a₂ * x) :=
        I_mul (I_mul I_two (frey_I_a₂ P)) hEx.I
      have h3 : I 0 (P.freyCurve⁄ℚ).a₄ := I_of_le (frey_I_a₄ P) (by norm_num)
      exact I_sub (I_add (I_add (I_of_le h1 (by norm_num)) (I_of_le h2 (by norm_num))) h3) hIy
    have hslope : (P.freyCurve⁄ℚ).slope x x y y =
        (3 * x ^ 2 + 2 * (P.freyCurve⁄ℚ).a₂ * x + (P.freyCurve⁄ℚ).a₄ -
          (P.freyCurve⁄ℚ).a₁ * y) / (x + 2 * y) := by
      rw [slope_of_Y_ne rfl hy, hD]
    set ℓ := (P.freyCurve⁄ℚ).slope x x y y with hℓ
    have hIℓ : I 0 ℓ := by
      rw [hslope]; have := I_div_E hN hED; simpa using this

    have hns₂ : (P.freyCurve⁄ℚ).Nonsingular ((P.freyCurve⁄ℚ).addX x x ℓ)
        ((P.freyCurve⁄ℚ).addY x x y ℓ) := nonsingular_add h h fun hxy => hy hxy.right
    set x₂ := (P.freyCurve⁄ℚ).addX x x ℓ with hx₂
    set y₂ := (P.freyCurve⁄ℚ).addY x x y ℓ with hy₂
    have hEx₂ : E 0 x₂ := by
      have hrw : x₂ = -(P.freyCurve⁄ℚ).a₂ + (ℓ * (ℓ + 1) - 2 * x) := by
        rw [hx₂]; simp only [addX, frey_a₁]; ring
      rw [hrw]
      exact E_add_I (E_neg hEA2) (I_sub (I_one_mul_add_one hIℓ) h2x) (by norm_num)
    have h2Q : Q + Q = .some x₂ y₂ hns₂ := by
      rw [hxy, add_self_of_Y_ne hy]
    have hIy₂ : I 0 y₂ := frey_I_y hns₂ hEx₂.I

    have hxx₂ : x₂ ≠ x := by
      intro hxe
      rcases (X_eq_iff (h₁ := hns₂) (h₂ := h)).mp hxe with he | he
      ·
        have hQQ : Q + Q = Q := by rw [h2Q, he, ← hxy]
        have hQ0 : Q = 0 := by
          have := congrArg (· - Q) hQQ
          simpa using this
        have : addOrderOf Q = 1 := by rw [hQ0]; simp
        omega
      ·
        have h3 : (3:ℕ) • Q = 0 := by
          rw [show (3:ℕ) = 2 + 1 from rfl, succ_nsmul, two_nsmul, h2Q, he, ← hxy, neg_add_cancel]
        have hdvd : P.p ∣ 3 := by rw [← hQ]; exact addOrderOf_dvd_iff_nsmul_eq_zero.mpr h3
        have := Nat.le_of_dvd (by norm_num) hdvd; omega

    have hdy : E 0 (y₂ - y) := by
      have hrw : y₂ - y = -x₂ + (-(ℓ * (x₂ - x)) - 2 * y) := by
        rw [hy₂, hx₂]; simp only [addY, negAddY, negY, addX, frey_a₁, frey_a₃]; ring
      rw [hrw]
      have hℓd : I 1 (ℓ * (x₂ - x)) := by
        have := I_mul hIℓ (I_one_sub_of_units hEx₂ hEx); simpa using this
      exact E_add_I (E_neg hEx₂) (I_sub (I_neg hℓd) h2y) (by norm_num)
    have hdx : E (v (x₂ - x)) (x₂ - x) := E_of_v (sub_ne_zero.mpr hxx₂)
    have hdx1 : 1 ≤ v (x₂ - x) := by
      rcases I_one_sub_of_units hEx₂ hEx with h0 | h0
      · exact absurd h0 (sub_ne_zero.mpr hxx₂)
      · exact h0
    have hμ : (P.freyCurve⁄ℚ).slope x₂ x y₂ y = (y₂ - y) / (x₂ - x) := slope_of_X_ne hxx₂
    set μ := (P.freyCurve⁄ℚ).slope x₂ x y₂ y with hμdef
    have hEμ : E (0 - v (x₂ - x)) μ := by rw [hμ]; exact E_div hdy hdx
    set m := (0 : ℤ) - v (x₂ - x) with hm
    have hEx₃ : E (m + m) ((P.freyCurve⁄ℚ).addX x₂ x μ) := by
      simp only [addX, frey_a₁, one_mul]
      exact E_sub_I (E_sub_I (E_sub_I (E_add_I (E_pow_two hEμ) hEμ.I (by omega))
        (frey_I_a₂ P) (by omega)) hEx₂.I (by omega)) hEx.I (by omega)

    have h3Q : (3:ℕ) • Q = .some _ _ (nonsingular_add hns₂ h fun hxy => hxx₂ hxy.left) := by
      rw [show (3:ℕ) = 2 + 1 from rfl, succ_nsmul, two_nsmul, h2Q, hxy, add_of_X_ne hxx₂]
    have hI3 := frey_I_xc_nsmul Q hQ 3
    rw [h3Q, xc_some] at hI3
    exact E_I_absurd hEx₃ hI3 (by omega)

end Orbit

section Algebra

theorem pm_core (x₁ y₁ x₂ y₂ a₂ a₄ : ℚ)
    (heq₁ : y₁ ^ 2 + x₁ * y₁ = x₁ ^ 3 + a₂ * x₁ ^ 2 + a₄ * x₁)
    (heq₂ : y₂ ^ 2 + x₂ * y₂ = x₂ ^ 3 + a₂ * x₂ ^ 2 + a₄ * x₂) :
    (4 * (y₁ - y₂) ^ 2 + 4 * (y₁ - y₂) * (x₁ - x₂) - 4 * (a₂ + x₁ + x₂) * (x₁ - x₂) ^ 2)
    * (4 * (y₁ + y₂ + x₂) ^ 2 + 4 * (y₁ + y₂ + x₂) * (x₁ - x₂) - 4 * (a₂ + x₁ + x₂) * (x₁ - x₂) ^ 2)
    = 16 * (x₁ * x₂ - a₄) ^ 2 * (x₁ - x₂) ^ 2 := by
  linear_combination
    (4 * (((x₁ + 2 * y₁) ^ 2 - (x₂ + 2 * y₂) ^ 2
        + (4 * x₁ ^ 3 + (1 + 4 * a₂) * x₁ ^ 2 + 4 * a₄ * x₁)
        - (4 * x₂ ^ 3 + (1 + 4 * a₂) * x₂ ^ 2 + 4 * a₄ * x₂))
        - 2 * (1 + 4 * a₂ + 4 * x₁ + 4 * x₂) * (x₁ - x₂) ^ 2)) * heq₁
    + (4 * (-((x₁ + 2 * y₁) ^ 2 - (x₂ + 2 * y₂) ^ 2
        + (4 * x₁ ^ 3 + (1 + 4 * a₂) * x₁ ^ 2 + 4 * a₄ * x₁)
        - (4 * x₂ ^ 3 + (1 + 4 * a₂) * x₂ ^ 2 + 4 * a₄ * x₂))
        - 2 * (1 + 4 * a₂ + 4 * x₁ + 4 * x₂) * (x₁ - x₂) ^ 2)) * heq₂

theorem pm_ident (x₁ y₁ x₂ y₂ a₂ a₄ : ℚ)
    (heq₁ : y₁ ^ 2 + x₁ * y₁ = x₁ ^ 3 + a₂ * x₁ ^ 2 + a₄ * x₁)
    (heq₂ : y₂ ^ 2 + x₂ * y₂ = x₂ ^ 3 + a₂ * x₂ ^ 2 + a₄ * x₂)
    (hd : x₁ - x₂ ≠ 0) :
    (((y₁ - y₂) / (x₁ - x₂)) ^ 2 + ((y₁ - y₂) / (x₁ - x₂)) - a₂ - x₁ - x₂)
      * (((y₁ - (-y₂ - x₂)) / (x₁ - x₂)) ^ 2 + ((y₁ - (-y₂ - x₂)) / (x₁ - x₂)) - a₂ - x₁ - x₂)
      * (x₁ - x₂) ^ 2 = (x₁ * x₂ - a₄) ^ 2 := by
  have key := pm_core x₁ y₁ x₂ y₂ a₂ a₄ heq₁ heq₂
  have hxp : ((y₁ - y₂) / (x₁ - x₂)) ^ 2 + ((y₁ - y₂) / (x₁ - x₂)) - a₂ - x₁ - x₂
      = (4 * (y₁ - y₂) ^ 2 + 4 * (y₁ - y₂) * (x₁ - x₂) - 4 * (a₂ + x₁ + x₂) * (x₁ - x₂) ^ 2)
        / (4 * (x₁ - x₂) ^ 2) := by
    field_simp
    ring
  have hxm : ((y₁ - (-y₂ - x₂)) / (x₁ - x₂)) ^ 2 + ((y₁ - (-y₂ - x₂)) / (x₁ - x₂)) - a₂ - x₁ - x₂
      = (4 * (y₁ + y₂ + x₂) ^ 2 + 4 * (y₁ + y₂ + x₂) * (x₁ - x₂)
          - 4 * (a₂ + x₁ + x₂) * (x₁ - x₂) ^ 2) / (4 * (x₁ - x₂) ^ 2) := by
    field_simp
    ring
  rw [hxp, hxm, div_mul_div_comm, key]
  field_simp
  ring

theorem dbl_ident (x y a₂ a₄ : ℚ) (heq : y ^ 2 + x * y = x ^ 3 + a₂ * x ^ 2 + a₄ * x)
    (hD : x + 2 * y ≠ 0) :
    (((3 * x ^ 2 + 2 * a₂ * x + a₄ - y) / (x + 2 * y)) ^ 2
      + ((3 * x ^ 2 + 2 * a₂ * x + a₄ - y) / (x + 2 * y)) - a₂ - x - x) * (x + 2 * y) ^ 2
      = (x ^ 2 - a₄) ^ 2 := by
  field_simp
  linear_combination (-1 - 4 * a₂ - 8 * x) * heq

theorem T0_ident (x y a₂ a₄ : ℚ) (heq : y ^ 2 + x * y = x ^ 3 + a₂ * x ^ 2 + a₄ * x)
    (hx : x ≠ 0) :
    ((y - 0) / (x - 0)) ^ 2 + (y - 0) / (x - 0) - a₂ - x - 0 = a₄ / x := by
  rw [sub_zero, sub_zero, sub_zero]
  field_simp
  linear_combination heq

end Algebra

section Node

variable {P : FreyPackage}

def gam (P : FreyPackage) : ℤ := (P.p : ℤ) * (padicValInt 2 P.b : ℤ) - 4

lemma frey_E_a₄' (P : FreyPackage) : E (gam P) (P.freyCurve⁄ℚ).a₄ := frey_E_a₄ P

lemma gam_pos (P : FreyPackage) : 1 ≤ gam P := frey_gamma_ge P

lemma frey_a₂_dichotomy (P : FreyPackage) :
    I 1 (P.freyCurve⁄ℚ).a₂ ∨ E 0 (P.freyCurve⁄ℚ).a₂ := by
  by_cases hA2 : I 1 (P.freyCurve⁄ℚ).a₂
  · exact Or.inl hA2
  · right
    refine ⟨fun h00 => hA2 (Or.inl h00), ?_⟩
    rcases frey_I_a₂ P with h0 | h0
    · exact absurd (Or.inl h0) hA2
    · by_contra hv; exact hA2 (Or.inr (by omega))

lemma frey_no_unit_point_split (hA2 : I 1 (P.freyCurve⁄ℚ).a₂) {x y : ℚ}
    (h : (P.freyCurve⁄ℚ).Nonsingular x y) (hEx : E 0 x) : False := by
  have hIy : I 0 y := frey_I_y h hEx.I
  have heq := frey_eqn P h
  have hL : I 1 (y ^ 2 + x * y) := by
    by_cases hyu : E 0 y
    · have hfac : y ^ 2 + x * y = y * (y + x) := by ring
      rw [hfac]
      have := I_mul hyu.I (I_one_add_of_units hyu hEx)
      simpa using this
    · have hy1 : I 1 y := by
        by_cases hy0 : y = 0
        · exact Or.inl hy0
        · rcases hIy with h0 | h0
          · exact absurd h0 hy0
          · have : v y ≠ 0 := fun hv => hyu ⟨hy0, hv⟩
            exact Or.inr (by omega)
      have hy2 : I (1 + 1) (y ^ 2) := I_pow_two hy1
      have hxy : I (0 + 1) (x * y) := I_mul hEx.I hy1
      exact I_add (I_of_le hy2 (by norm_num)) (I_of_le hxy (by norm_num))
  have hR : E 0 (x ^ 3 + (P.freyCurve⁄ℚ).a₂ * x ^ 2 + (P.freyCurve⁄ℚ).a₄ * x) := by
    have h3 : E 0 (x ^ 3) := by have := E_pow hEx 3; simpa using this
    have h2 : I (1 + (0 + 0)) ((P.freyCurve⁄ℚ).a₂ * x ^ 2) := I_mul hA2 (I_pow_two hEx.I)
    have h1 : I (1 + 0) ((P.freyCurve⁄ℚ).a₄ * x) := I_mul (frey_I_a₄ P) hEx.I
    exact E_add_I (E_add_I h3 h2 (by norm_num)) h1 (by norm_num)
  rw [heq] at hL
  exact E_I_absurd hR hL (by norm_num)

lemma frey_unit_double_nonsplit (hEA2 : E 0 (P.freyCurve⁄ℚ).a₂) {x y : ℚ}
    (h : (P.freyCurve⁄ℚ).Nonsingular x y) (hEx : E 0 x) :
    y ≠ (P.freyCurve⁄ℚ).negY x y ∧
    E 0 ((P.freyCurve⁄ℚ).addX x x ((P.freyCurve⁄ℚ).slope x x y y)) := by
  have hIy : I 0 y := frey_I_y h hEx.I
  have hD : y - (P.freyCurve⁄ℚ).negY x y = x + 2 * y := by rw [frey_negY]; ring
  have h2y : I 1 (2 * y) := by have := I_mul I_two hIy; simpa using this
  have h2x : I 1 (2 * x) := by have := I_mul I_two hEx.I; simpa using this
  have hED : E 0 (x + 2 * y) := E_add_I hEx h2y (by norm_num)
  have hy : y ≠ (P.freyCurve⁄ℚ).negY x y := by
    intro hyy; apply hED.1; rw [← hD]; exact sub_eq_zero.mpr hyy
  refine ⟨hy, ?_⟩
  have hN : I 0 (3 * x ^ 2 + 2 * (P.freyCurve⁄ℚ).a₂ * x + (P.freyCurve⁄ℚ).a₄ -
      (P.freyCurve⁄ℚ).a₁ * y) := by
    rw [frey_a₁, one_mul]
    have h1 : I (0 + (0 + 0)) (3 * x ^ 2) := I_mul E_three.I (I_pow_two hEx.I)
    have h2 : I (1 + 0 + 0) (2 * (P.freyCurve⁄ℚ).a₂ * x) :=
      I_mul (I_mul I_two (frey_I_a₂ P)) hEx.I
    have h3 : I 0 (P.freyCurve⁄ℚ).a₄ := I_of_le (frey_I_a₄ P) (by norm_num)
    exact I_sub (I_add (I_add (I_of_le h1 (by norm_num)) (I_of_le h2 (by norm_num))) h3) hIy
  have hslope : (P.freyCurve⁄ℚ).slope x x y y =
      (3 * x ^ 2 + 2 * (P.freyCurve⁄ℚ).a₂ * x + (P.freyCurve⁄ℚ).a₄ -
        (P.freyCurve⁄ℚ).a₁ * y) / (x + 2 * y) := by
    rw [slope_of_Y_ne rfl hy, hD]
  have hIℓ : I 0 ((P.freyCurve⁄ℚ).slope x x y y) := by
    rw [hslope]; have := I_div_E hN hED; simpa using this
  have hrw : (P.freyCurve⁄ℚ).addX x x ((P.freyCurve⁄ℚ).slope x x y y) =
      -(P.freyCurve⁄ℚ).a₂ + ((P.freyCurve⁄ℚ).slope x x y y *
        ((P.freyCurve⁄ℚ).slope x x y y + 1) - 2 * x) := by
    simp only [addX, frey_a₁]; ring
  rw [hrw]
  exact E_add_I (E_neg hEA2) (I_sub (I_one_mul_add_one hIℓ) h2x) (by norm_num)

lemma frey_ns00 (P : FreyPackage) : (P.freyCurve⁄ℚ).Nonsingular 0 0 := by
  rw [nonsingular_zero]
  exact ⟨frey_a₆ P, Or.inr (frey_E_a₄ P).1⟩

lemma frey_T0_T0 (P : FreyPackage) :
    Point.some 0 0 (frey_ns00 P) + Point.some 0 0 (frey_ns00 P) = 0 :=
  add_self_of_Y_eq (by rw [frey_negY]; norm_num)

lemma frey_addX_T0 {x y : ℚ} (h : (P.freyCurve⁄ℚ).Nonsingular x y) (hx0 : x ≠ 0) :
    (P.freyCurve⁄ℚ).addX x 0 ((P.freyCurve⁄ℚ).slope x 0 y 0) = (P.freyCurve⁄ℚ).a₄ / x := by
  have heq := frey_eqn P h
  rw [slope_of_X_ne hx0]
  simp only [addX, frey_a₁, one_mul]
  set A2 := (P.freyCurve⁄ℚ).a₂ with hA2
  set A4 := (P.freyCurve⁄ℚ).a₄ with hA4
  exact T0_ident x y A2 A4 heq hx0

lemma frey_dbl_ident {x y : ℚ} (h : (P.freyCurve⁄ℚ).Nonsingular x y)
    (hy : y ≠ (P.freyCurve⁄ℚ).negY x y) :
    (P.freyCurve⁄ℚ).addX x x ((P.freyCurve⁄ℚ).slope x x y y) * (x + 2 * y) ^ 2 =
      (x ^ 2 - (P.freyCurve⁄ℚ).a₄) ^ 2 := by
  have heq := frey_eqn P h
  have hD : y - (P.freyCurve⁄ℚ).negY x y = x + 2 * y := by rw [frey_negY]; ring
  have hD0 : x + 2 * y ≠ 0 := by rw [← hD]; exact sub_ne_zero.mpr hy
  rw [slope_of_Y_ne rfl hy, hD]
  simp only [addX, frey_a₁, one_mul]
  set A2 := (P.freyCurve⁄ℚ).a₂ with hA2
  set A4 := (P.freyCurve⁄ℚ).a₄ with hA4
  exact dbl_ident x y A2 A4 heq hD0

lemma frey_pm_ident {x₁ y₁ x₂ y₂ : ℚ} (h₁ : (P.freyCurve⁄ℚ).Nonsingular x₁ y₁)
    (h₂ : (P.freyCurve⁄ℚ).Nonsingular x₂ y₂) (hx : x₁ ≠ x₂) :
    (P.freyCurve⁄ℚ).addX x₁ x₂ ((P.freyCurve⁄ℚ).slope x₁ x₂ y₁ y₂) *
      (P.freyCurve⁄ℚ).addX x₁ x₂ ((P.freyCurve⁄ℚ).slope x₁ x₂ y₁ ((P.freyCurve⁄ℚ).negY x₂ y₂)) *
      (x₁ - x₂) ^ 2 = (x₁ * x₂ - (P.freyCurve⁄ℚ).a₄) ^ 2 := by
  have heq₁ := frey_eqn P h₁
  have heq₂ := frey_eqn P h₂
  rw [slope_of_X_ne hx, slope_of_X_ne hx, frey_negY]
  simp only [addX, frey_a₁, one_mul]
  set A2 := (P.freyCurve⁄ℚ).a₂ with hA2
  set A4 := (P.freyCurve⁄ℚ).a₄ with hA4
  exact pm_ident x₁ y₁ x₂ y₂ A2 A4 heq₁ heq₂ (sub_ne_zero.mpr hx)

lemma frey_order_nsmul (Q : (P.freyCurve⁄ℚ).Point) (hQ : addOrderOf Q = P.p) {k : ℕ}
    (hk : ¬ P.p ∣ k) : addOrderOf (k • Q) = P.p := by
  haveI : Fact P.p.Prime := ⟨P.pp⟩
  apply addOrderOf_eq_prime
  · rw [← mul_nsmul, mul_comm, mul_nsmul, ← hQ, addOrderOf_nsmul_eq_zero, nsmul_zero]
  · intro h0
    apply hk
    rw [← hQ]; exact addOrderOf_dvd_iff_nsmul_eq_zero.mpr h0

theorem frey_shallow_of_order (Q : (P.freyCurve⁄ℚ).Point) (hQ : addOrderOf Q = P.p) {x y : ℚ}
    {h : (P.freyCurve⁄ℚ).Nonsingular x y} (hxy : Q = .some x y h) : v x ≤ gam P - 1 := by
  classical
  have hp5 := P.hp5
  by_contra hle
  push Not at hle
  have hx0 : x ≠ 0 := frey_x_ne_zero_of_order Q hQ hxy
  have hEx : E (v x) x := E_of_v hx0

  set T0 : (P.freyCurve⁄ℚ).Point := Point.some 0 0 (frey_ns00 P) with hT0
  have hns' : (P.freyCurve⁄ℚ).Nonsingular ((P.freyCurve⁄ℚ).addX x 0 ((P.freyCurve⁄ℚ).slope x 0 y 0))
      ((P.freyCurve⁄ℚ).addY x 0 y ((P.freyCurve⁄ℚ).slope x 0 y 0)) :=
    nonsingular_add h (frey_ns00 P) fun hxy => hx0 hxy.left
  set x' := (P.freyCurve⁄ℚ).addX x 0 ((P.freyCurve⁄ℚ).slope x 0 y 0) with hx'
  set y' := (P.freyCurve⁄ℚ).addY x 0 y ((P.freyCurve⁄ℚ).slope x 0 y 0) with hy'
  have hR' : Q + T0 = Point.some x' y' hns' := by rw [hxy, hT0]; exact add_of_X_ne hx0
  have hx'v : x' = (P.freyCurve⁄ℚ).a₄ / x := by rw [hx']; exact frey_addX_T0 h hx0
  have hEx' : E (gam P - v x) x' := by rw [hx'v]; exact E_div (frey_E_a₄' P) hEx

  have h2R' : (Q + T0) + (Q + T0) = (2:ℕ) • Q := by
    rw [two_nsmul, add_add_add_comm, hT0, frey_T0_T0, add_zero]
  have h2Q0 : (2:ℕ) • Q ≠ 0 := by
    intro h0
    have hdvd : P.p ∣ 2 := by rw [← hQ]; exact addOrderOf_dvd_iff_nsmul_eq_zero.mpr h0
    have := Nat.le_of_dvd (by norm_num) hdvd; omega
  have h2ord : addOrderOf ((2:ℕ) • Q) = P.p :=
    frey_order_nsmul Q hQ (fun hdvd => by have := Nat.le_of_dvd (by norm_num) hdvd; omega)
  rcases lt_or_eq_of_le (show gam P - v x ≤ 0 by omega) with hneg | hzero
  ·
    have hy'' : y' ≠ (P.freyCurve⁄ℚ).negY x' y' := by
      intro hyy
      apply h2Q0
      rw [← h2R', hR', add_self_of_Y_eq hyy]
    obtain ⟨hne3, hv3⟩ := frey_double_neg hns' hEx' hneg hy''
    have hsum : (2:ℕ) • Q = Point.some _ _ (nonsingular_add hns' hns' fun hxy => hy'' hxy.right) := by
      rw [← h2R', hR', add_self_of_Y_ne hy'']
    have hI := frey_I_xc_nsmul Q hQ 2
    rw [hsum, xc_some] at hI
    rcases hI with h0 | h0
    · exact hne3 h0
    · omega
  ·
    rw [hzero] at hEx'
    rcases frey_a₂_dichotomy P with hA2 | hEA2
    · exact frey_no_unit_point_split hA2 hns' hEx'
    · obtain ⟨hy'', hE2⟩ := frey_unit_double_nonsplit hEA2 hns' hEx'
      have hsum : (2:ℕ) • Q = Point.some _ _ (nonsingular_add hns' hns' fun hxy => hy'' hxy.right) := by
        rw [← h2R', hR', add_self_of_Y_ne hy'']
      have hdeep := frey_deep_of_order ((2:ℕ) • Q) h2ord hsum
      rw [hE2.2] at hdeep
      omega

theorem frey_E_D (Q : (P.freyCurve⁄ℚ).Point) (hQ : addOrderOf Q = P.p) {x y : ℚ}
    {h : (P.freyCurve⁄ℚ).Nonsingular x y} (hxy : Q = .some x y h) : E (v x) (x + 2 * y) := by
  have hx0 : x ≠ 0 := frey_x_ne_zero_of_order Q hQ hxy
  have hEx : E (v x) x := E_of_v hx0
  have hlo : 1 ≤ v x := frey_deep_of_order Q hQ hxy
  have hhi : v x ≤ gam P - 1 := frey_shallow_of_order Q hQ hxy
  set e := v x with he
  have heq := frey_eqn P h
  have hD2 : (x + 2 * y) ^ 2 =
      4 * x ^ 3 + (1 + 4 * (P.freyCurve⁄ℚ).a₂) * x ^ 2 + 4 * (P.freyCurve⁄ℚ).a₄ * x := by
    linear_combination 4 * heq
  have hunit : E 0 (1 + 4 * (P.freyCurve⁄ℚ).a₂) := by
    have h1 : E 0 (1 : ℚ) := ⟨one_ne_zero, padicValRat.one⟩
    have h4 : I (2 + 0) (4 * (P.freyCurve⁄ℚ).a₂) := I_mul E_four.I (frey_I_a₂ P)
    exact E_add_I h1 h4 (by norm_num)
  have hmain : E (0 + (e + e)) ((1 + 4 * (P.freyCurve⁄ℚ).a₂) * x ^ 2) :=
    E_mul hunit (E_pow_two hEx)
  have h3 : I (2 + (e + (e + e))) (4 * x ^ 3) := by
    have := I_mul E_four.I (I_mul hEx.I (I_pow_two hEx.I))
    rw [← pow_succ'] at this; simpa using this
  have h1 : I (2 + gam P + e) (4 * (P.freyCurve⁄ℚ).a₄ * x) :=
    I_mul (I_mul E_four.I (frey_E_a₄' P).I) hEx.I
  have hE2 : E (e + e) ((x + 2 * y) ^ 2) := by
    rw [hD2]
    have := E_add_I (I_add_E h3 hmain (by omega)) h1 (by omega)
    simpa using this
  refine ⟨fun h0 => hE2.1 (by rw [h0]; ring), ?_⟩
  have h2 := hE2.2
  rw [padicValRat.pow _] at h2
  push_cast at h2
  omega

end Node

section Arith

lemma wrap_cases {γ t : ℤ} (hγ : 0 < γ) (hdvd : 2 * γ ∣ t) (h1 : -4 * γ < t) (h2 : t < 2 * γ) :
    t = 0 ∨ t = -(2 * γ) := by
  obtain ⟨q, hq⟩ := hdvd
  have hq1 : q < 1 := by
    by_contra h; push Not at h; nlinarith
  have hq2 : -2 < q := by
    by_contra h; push Not at h; nlinarith
  have : q = 0 ∨ q = -1 := by omega
  rcases this with rfl | rfl
  · left; rw [hq]; ring
  · right; rw [hq]; ring

lemma wrap_zero {γ t : ℤ} (hγ : 0 < γ) (hdvd : 2 * γ ∣ t) (h1 : -(2 * γ) < t) (h2 : t < 2 * γ) :
    t = 0 := by
  obtain ⟨q, hq⟩ := hdvd
  have hq1 : q < 1 := by
    by_contra h; push Not at h; nlinarith
  have hq2 : -1 < q := by
    by_contra h; push Not at h; nlinarith
  have : q = 0 := by omega
  rw [hq, this]; ring

theorem arith_core (p : ℕ) (hp5 : 5 ≤ p) (γ : ℤ) (e A B : ℕ → ℤ) (A₁ : ℤ)
    (hbd : ∀ k, 1 ≤ k → k ≤ p - 1 → 1 ≤ e k ∧ e k ≤ γ - 1)
    (hA₁ : (2 * e 1 ≠ γ → A₁ = min (2 * e 1) γ) ∧ (2 * e 1 = γ → γ ≤ A₁))
    (h2 : e 2 + 2 * e 1 = 2 * A₁)
    (hA : ∀ k, 2 ≤ k → k ≤ p - 2 →
      (e k + e 1 ≠ γ → A k = min (e k + e 1) γ) ∧ (e k + e 1 = γ → γ ≤ A k))
    (hB : ∀ k, 2 ≤ k → k ≤ p - 2 →
      (e k ≠ e 1 → B k = min (e k) (e 1)) ∧ (e k = e 1 → e 1 ≤ B k))
    (hrec : ∀ k, 2 ≤ k → k ≤ p - 2 → e (k + 1) + e (k - 1) + 2 * B k = 2 * A k)
    (hend : e (p - 1) = e 1)
    (hdiv : ∀ m : ℤ, 2 * γ ∣ (p : ℤ) * m → 2 * γ ∣ m) : False := by
  set ε := e 1 with hε
  have hε1 : 1 ≤ ε ∧ ε ≤ γ - 1 := hbd 1 le_rfl (by omega)
  have hγ : 0 < γ := by omega

  have h2ne : 2 * ε ≠ γ := by
    intro h2eq
    have := hA₁.2 h2eq
    have hb2 := hbd 2 (by norm_num) (by omega)
    omega
  have hA₁' : A₁ = min (2 * ε) γ := hA₁.1 h2ne

  have claim : ∀ k, 1 ≤ k → k ≤ p - 1 →
      ∃ θ : ℤ, 2 * γ ∣ θ - (k : ℤ) * ε ∧ -γ < θ ∧ θ ≤ γ ∧ (e k = θ ∨ e k = -θ) := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro hk1 hkp
      rcases Nat.lt_or_ge k 3 with hk3 | hk3
      ·
        interval_cases k
        · exact ⟨ε, by simp, by omega, by omega, Or.inl rfl⟩
        ·
          have hb2 := hbd 2 (by norm_num) hkp
          by_cases hlt : 2 * ε < γ
          · refine ⟨2 * ε, by simp, by omega, by omega, Or.inl ?_⟩
            rw [min_eq_left hlt.le] at hA₁'
            omega
          · refine ⟨2 * ε - 2 * γ, ⟨-1, by push_cast; ring⟩, by omega, by omega, Or.inr ?_⟩
            rw [min_eq_right (by omega)] at hA₁'
            omega
      ·
        obtain ⟨θ, hθd, hθ1, hθ2, hθe⟩ := ih (k - 1) (by omega) (by omega) (by omega)
        obtain ⟨θ', hθ'd, hθ'1, hθ'2, hθ'e⟩ := ih (k - 2) (by omega) (by omega) (by omega)
        have hbk := hbd k hk1 hkp
        have hbj := hbd (k - 1) (by omega) (by omega)
        have hbj' := hbd (k - 2) (by omega) (by omega)
        have hr := hrec (k - 1) (by omega) (by omega)
        rw [show k - 1 + 1 = k by omega, show k - 1 - 1 = k - 2 by omega] at hr
        have hAk := hA (k - 1) (by omega) (by omega)
        have hBk := hB (k - 1) (by omega) (by omega)

        have hcast : ((k - 1 : ℕ) : ℤ) = ((k - 2 : ℕ) : ℤ) + 1 := by omega
        have hdd : 2 * γ ∣ θ - θ' - ε := by
          have : θ - θ' - ε = (θ - ((k - 1 : ℕ) : ℤ) * ε) - (θ' - ((k - 2 : ℕ) : ℤ) * ε) := by
            rw [hcast]; ring
          rw [this]; exact dvd_sub hθd hθ'd
        have hwrap := wrap_cases hγ hdd (by omega) (by omega)

        have hcast' : ((k : ℕ) : ℤ) = ((k - 1 : ℕ) : ℤ) + 1 := by omega
        have hdvdp : 2 * γ ∣ (θ + ε) - (k : ℤ) * ε := by
          have : (θ + ε) - (k : ℤ) * ε = θ - ((k - 1 : ℕ) : ℤ) * ε := by rw [hcast']; ring
          rw [this]; exact hθd
        have hdvdm : 2 * γ ∣ (θ + ε - 2 * γ) - (k : ℤ) * ε := by
          have : (θ + ε - 2 * γ) - (k : ℤ) * ε = (θ - ((k - 1 : ℕ) : ℤ) * ε) - 2 * γ := by
            rw [hcast']; ring
          rw [this]; exact dvd_sub hθd (dvd_refl _)

        by_cases hdeg1 : e (k - 1) = ε
        ·
          exfalso
          have hB' := hBk.2 hdeg1
          rcases hθe with hθe | hθe
          ·
            by_cases hθε : θ = ε
            ·
              rcases hwrap with hw | hw <;> omega
            ·
              omega
          ·
            have hθε : θ = -ε := by omega
            have hA' : A (k - 1) = min (e (k - 1) + ε) γ := hAk.1 (by omega)
            rw [hdeg1] at hA'
            rcases le_or_gt (ε + ε) γ with h | h
            · rw [min_eq_left h] at hA'
              rcases hwrap with hw | hw <;> omega
            · rw [min_eq_right h.le] at hA'
              rcases hwrap with hw | hw <;> omega
        by_cases hdeg2 : e (k - 1) + ε = γ
        ·
          exfalso
          have hA' := hAk.2 hdeg2
          have hB' : B (k - 1) = min (e (k - 1)) ε := hBk.1 hdeg1
          rcases hθe with hθe | hθe
          ·
            rcases le_or_gt (e (k - 1)) ε with h | h
            · rw [min_eq_left h] at hB'
              rcases hwrap with hw | hw <;> omega
            · rw [min_eq_right h.le] at hB'
              rcases hwrap with hw | hw <;> omega
          ·
            rcases hwrap with hw | hw <;> omega

        have hA' : A (k - 1) = min (e (k - 1) + ε) γ := hAk.1 hdeg2
        have hB' : B (k - 1) = min (e (k - 1)) ε := hBk.1 hdeg1
        by_cases hup : θ + ε ≤ γ
        · refine ⟨θ + ε, hdvdp, by omega, hup, ?_⟩
          rcases le_or_gt (e (k - 1) + ε) γ with h | h <;>
            rcases le_or_gt (e (k - 1)) ε with h' | h'
          · rw [min_eq_left h] at hA'; rw [min_eq_left h'] at hB'
            rcases hθe with hθe | hθe <;> rcases hwrap with hw | hw <;> omega
          · rw [min_eq_left h] at hA'; rw [min_eq_right h'.le] at hB'
            rcases hθe with hθe | hθe <;> rcases hwrap with hw | hw <;> omega
          · rw [min_eq_right h.le] at hA'; rw [min_eq_left h'] at hB'
            rcases hθe with hθe | hθe <;> rcases hwrap with hw | hw <;> omega
          · rw [min_eq_right h.le] at hA'; rw [min_eq_right h'.le] at hB'
            rcases hθe with hθe | hθe <;> rcases hwrap with hw | hw <;> omega
        · refine ⟨θ + ε - 2 * γ, hdvdm, by omega, by omega, ?_⟩
          rcases le_or_gt (e (k - 1) + ε) γ with h | h <;>
            rcases le_or_gt (e (k - 1)) ε with h' | h'
          · rw [min_eq_left h] at hA'; rw [min_eq_left h'] at hB'
            rcases hθe with hθe | hθe <;> rcases hwrap with hw | hw <;> omega
          · rw [min_eq_left h] at hA'; rw [min_eq_right h'.le] at hB'
            rcases hθe with hθe | hθe <;> rcases hwrap with hw | hw <;> omega
          · rw [min_eq_right h.le] at hA'; rw [min_eq_left h'] at hB'
            rcases hθe with hθe | hθe <;> rcases hwrap with hw | hw <;> omega
          · rw [min_eq_right h.le] at hA'; rw [min_eq_right h'.le] at hB'
            rcases hθe with hθe | hθe <;> rcases hwrap with hw | hw <;> omega

  obtain ⟨θ, hθd, hθ1, hθ2, hθe⟩ := claim (p - 1) (by omega) le_rfl
  obtain ⟨θ'', hθ''d, hθ''1, hθ''2, hθ''e⟩ := claim (p - 2) (by omega) (by omega)
  have hbp2 := hbd (p - 2) (by omega) (by omega)
  rw [hend] at hθe
  have hcast : ((p - 1 : ℕ) : ℤ) = ((p - 2 : ℕ) : ℤ) + 1 := by omega
  have hcastp : ((p : ℕ) : ℤ) = ((p - 1 : ℕ) : ℤ) + 1 := by omega
  rcases hθe with hθe | hθe
  ·
    have hdd : 2 * γ ∣ θ'' := by
      have : θ'' = (θ'' - ((p - 2 : ℕ) : ℤ) * ε) - (θ - ((p - 1 : ℕ) : ℤ) * ε) + (θ - ε) := by
        rw [hcast]; ring
      have h0 : θ - ε = 0 := by omega
      rw [this, h0, add_zero]
      exact dvd_sub hθ''d hθd
    have := wrap_zero hγ hdd (by omega) (by omega)
    omega
  ·
    have hdd : 2 * γ ∣ (p : ℤ) * ε := by
      have : (p : ℤ) * ε = -(θ - ((p - 1 : ℕ) : ℤ) * ε) + (θ + ε) := by
        rw [hcastp]; ring
      rw [this, show θ + ε = 0 by omega, add_zero]
      exact (dvd_neg).mpr hθd
    have hε2 := hdiv ε hdd
    have := wrap_zero hγ hε2 (by omega) (by omega)
    omega

end Arith

theorem frey_no_rational_p_torsion (P : FreyPackage) (Q : (P.freyCurve⁄ℚ).Point)
    (hQp : P.p • Q = 0) : Q = 0 := by
  classical
  by_contra hQ0
  haveI : Fact P.p.Prime := ⟨P.pp⟩
  have hp5 := P.hp5
  have hpp := P.pp
  have hQ : addOrderOf Q = P.p := addOrderOf_eq_prime hQp hQ0
  rcases hQdef : Q with _ | ⟨x₁, y₁, h₁⟩
  · exact hQ0 (by rw [hQdef]; rfl)
  have hx₁0 : x₁ ≠ 0 := frey_x_ne_zero_of_order Q hQ hQdef
  have hEx₁ : E (v x₁) x₁ := E_of_v hx₁0

  set e : ℕ → ℤ := fun k => v (xc P (k • Q)) with he
  set A : ℕ → ℤ := fun k => v (xc P (k • Q) * x₁ - (P.freyCurve⁄ℚ).a₄) with hA
  set B : ℕ → ℤ := fun k => v (xc P (k • Q) - x₁) with hB
  set A₁ : ℤ := v (x₁ ^ 2 - (P.freyCurve⁄ℚ).a₄) with hA₁
  have he1 : e 1 = v x₁ := by
    show v (xc P (1 • Q)) = v x₁
    rw [one_nsmul, hQdef, xc_some]

  have key : ∀ k, ¬ P.p ∣ k → ∃ xk yk hk, k • Q = Point.some xk yk hk ∧ e k = v xk ∧
      1 ≤ v xk ∧ v xk ≤ gam P - 1 ∧ xk ≠ 0 := by
    intro k hk
    rcases hK : k • Q with _ | ⟨xk, yk, hk'⟩
    · exfalso
      apply hk
      rw [← hQ]
      exact addOrderOf_dvd_iff_nsmul_eq_zero.mpr (by rw [hK]; rfl)
    have hord : addOrderOf (Point.some xk yk hk') = P.p := by
      rw [← hK]; exact frey_order_nsmul Q hQ hk
    have hek : e k = v xk := by
      show v (xc P (k • Q)) = v xk
      rw [hK, xc_some]
    exact ⟨xk, yk, hk', rfl, hek, frey_deep_of_order _ hord rfl, frey_shallow_of_order _ hord rfl,
      frey_x_ne_zero_of_order _ hord rfl⟩

  have hbd : ∀ k, 1 ≤ k → k ≤ P.p - 1 → 1 ≤ e k ∧ e k ≤ gam P - 1 := by
    intro k hk1 hkp
    obtain ⟨xk, yk, hk, -, hek, hlo, hhi, -⟩ :=
      key k (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))
    rw [hek]; exact ⟨hlo, hhi⟩

  have hD := frey_E_D Q hQ hQdef
  have hDform : y₁ - (P.freyCurve⁄ℚ).negY x₁ y₁ = x₁ + 2 * y₁ := by rw [frey_negY]; ring
  have hy₁ : y₁ ≠ (P.freyCurve⁄ℚ).negY x₁ y₁ := by
    intro hyy; apply hD.1; rw [← hDform]; exact sub_eq_zero.mpr hyy
  have hns₂ := nonsingular_add h₁ h₁ fun hxy => hy₁ hxy.right
  have h2nd : ¬ P.p ∣ 2 := fun hdvd => by have := Nat.le_of_dvd (by norm_num) hdvd; omega
  have h2Q : (2:ℕ) • Q = Point.some _ _ hns₂ := by
    rw [two_nsmul, hQdef, add_self_of_Y_ne hy₁]
  have hx₂0 : (P.freyCurve⁄ℚ).addX x₁ x₁ ((P.freyCurve⁄ℚ).slope x₁ x₁ y₁ y₁) ≠ 0 :=
    frey_x_ne_zero_of_order ((2:ℕ) • Q) (frey_order_nsmul Q hQ h2nd) h2Q
  have hidentD := frey_dbl_ident h₁ hy₁
  have hsq0 : x₁ ^ 2 - (P.freyCurve⁄ℚ).a₄ ≠ 0 := by
    intro h0
    rw [h0] at hidentD
    exact (mul_ne_zero hx₂0 (pow_ne_zero 2 hD.1)) (by rw [hidentD]; ring)
  have hvalD : v ((P.freyCurve⁄ℚ).addX x₁ x₁ ((P.freyCurve⁄ℚ).slope x₁ x₁ y₁ y₁)) +
      2 * v x₁ = 2 * A₁ := by
    have := congrArg (padicValRat 2) hidentD
    rw [padicValRat.mul hx₂0 (pow_ne_zero 2 hD.1), padicValRat.pow _,
      padicValRat.pow _, hD.2] at this
    push_cast at this
    show _ = 2 * v (x₁ ^ 2 - (P.freyCurve⁄ℚ).a₄)
    linarith

  have h2 : e 2 + 2 * e 1 = 2 * A₁ := by
    have he2 : e 2 = v ((P.freyCurve⁄ℚ).addX x₁ x₁ ((P.freyCurve⁄ℚ).slope x₁ x₁ y₁ y₁)) := by
      show v (xc P (2 • Q)) = _
      rw [h2Q, xc_some]
    rw [he2, he1]; exact hvalD
  have hA₁spec : (2 * e 1 ≠ gam P → A₁ = min (2 * e 1) (gam P)) ∧
      (2 * e 1 = gam P → gam P ≤ A₁) := by
    have hsq : E (v x₁ + v x₁) (x₁ ^ 2) := E_pow_two hEx₁
    constructor
    · intro hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · rw [min_eq_left hlt.le]
        have := (E_sub_I hsq (frey_E_a₄' P).I (by rw [he1] at hlt; omega)).2
        show v (x₁ ^ 2 - (P.freyCurve⁄ℚ).a₄) = _
        rw [this, he1]; ring
      · rw [min_eq_right hgt.le]
        have := (I_sub_E hsq.I (frey_E_a₄' P) (by rw [he1] at hgt; omega)).2
        show v (x₁ ^ 2 - (P.freyCurve⁄ℚ).a₄) = _
        rw [this]
    · intro heqγ
      have hsq' : I (gam P) (x₁ ^ 2) := by
        have : v x₁ + v x₁ = gam P := by rw [he1] at heqγ; omega
        rw [← this]; exact hsq.I
      rcases I_sub hsq' (frey_E_a₄' P).I with h0 | h0
      · exact absurd h0 hsq0
      · exact h0

  have pkg : ∀ k, 2 ≤ k → k ≤ P.p - 2 →
      (e (k + 1) + e (k - 1) + 2 * B k = 2 * A k) ∧
      ((e k + e 1 ≠ gam P → A k = min (e k + e 1) (gam P)) ∧ (e k + e 1 = gam P → gam P ≤ A k)) ∧
      ((e k ≠ e 1 → B k = min (e k) (e 1)) ∧ (e k = e 1 → e 1 ≤ B k)) := by
    intro k hk2 hkp
    have hk : ¬ P.p ∣ k := Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
    have hkp1 : ¬ P.p ∣ k + 1 := Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
    have hkm1 : ¬ P.p ∣ k - 1 := Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
    obtain ⟨xk, yk, hk', hK, hek, hlo, hhi, hxk0⟩ := key k hk

    have hne : xk ≠ x₁ := by
      intro hxe
      rcases (X_eq_iff (h₁ := hk') (h₂ := h₁)).mp hxe with heq' | heq'
      · have h0 : (k - 1) • Q = 0 := by
          have h' : (k - 1) • Q + Q = k • Q := by
            rw [← succ_nsmul, Nat.sub_add_cancel (by omega)]
          rw [hK, heq', ← hQdef] at h'
          have := congrArg (· - Q) h'
          simpa using this
        exact hkm1 (by rw [← hQ]; exact addOrderOf_dvd_iff_nsmul_eq_zero.mpr h0)
      · have h0 : (k + 1) • Q = 0 := by rw [succ_nsmul, hK, heq', ← hQdef, neg_add_cancel]
        exact hkp1 (by rw [← hQ]; exact addOrderOf_dvd_iff_nsmul_eq_zero.mpr h0)

    have hnsp := nonsingular_add hk' h₁ fun hxy => hne hxy.left
    have hKp : (k + 1) • Q = Point.some _ _ hnsp := by
      rw [succ_nsmul, hK, hQdef, add_of_X_ne hne]
    have hneg₁ : (P.freyCurve⁄ℚ).Nonsingular x₁ ((P.freyCurve⁄ℚ).negY x₁ y₁) :=
      (nonsingular_neg x₁ y₁).mpr h₁
    have hnsm := nonsingular_add hk' hneg₁ fun hxy => hne hxy.left
    have hKm : (k - 1) • Q = Point.some _ _ hnsm := by
      have h' : (k - 1) • Q = k • Q + -Q := by
        rw [← sub_eq_add_neg, eq_sub_iff_add_eq, ← succ_nsmul, Nat.sub_add_cancel (by omega)]
      rw [h', hK, hQdef, neg_some, add_of_X_ne hne]
    have hxp0 : (P.freyCurve⁄ℚ).addX xk x₁ ((P.freyCurve⁄ℚ).slope xk x₁ yk y₁) ≠ 0 :=
      frey_x_ne_zero_of_order ((k + 1) • Q) (frey_order_nsmul Q hQ hkp1) hKp
    have hxm0 : (P.freyCurve⁄ℚ).addX xk x₁
        ((P.freyCurve⁄ℚ).slope xk x₁ yk ((P.freyCurve⁄ℚ).negY x₁ y₁)) ≠ 0 :=
      frey_x_ne_zero_of_order ((k - 1) • Q) (frey_order_nsmul Q hQ hkm1) hKm
    have hident := frey_pm_ident hk' h₁ hne
    have hd0 : xk - x₁ ≠ 0 := sub_ne_zero.mpr hne
    have hc0 : xk * x₁ - (P.freyCurve⁄ℚ).a₄ ≠ 0 := by
      intro h0
      rw [h0] at hident
      exact (mul_ne_zero (mul_ne_zero hxp0 hxm0) (pow_ne_zero 2 hd0)) (by rw [hident]; ring)
    have hval : v ((P.freyCurve⁄ℚ).addX xk x₁ ((P.freyCurve⁄ℚ).slope xk x₁ yk y₁)) +
        v ((P.freyCurve⁄ℚ).addX xk x₁
          ((P.freyCurve⁄ℚ).slope xk x₁ yk ((P.freyCurve⁄ℚ).negY x₁ y₁))) +
        2 * v (xk - x₁) = 2 * v (xk * x₁ - (P.freyCurve⁄ℚ).a₄) := by
      have := congrArg (padicValRat 2) hident
      rw [padicValRat.mul (mul_ne_zero hxp0 hxm0) (pow_ne_zero 2 hd0), padicValRat.mul hxp0 hxm0,
        padicValRat.pow _, padicValRat.pow _] at this
      push_cast at this
      linarith
    have hep : e (k + 1) = v ((P.freyCurve⁄ℚ).addX xk x₁ ((P.freyCurve⁄ℚ).slope xk x₁ yk y₁)) := by
      show v (xc P ((k + 1) • Q)) = _
      rw [hKp, xc_some]
    have hem : e (k - 1) = v ((P.freyCurve⁄ℚ).addX xk x₁
        ((P.freyCurve⁄ℚ).slope xk x₁ yk ((P.freyCurve⁄ℚ).negY x₁ y₁))) := by
      show v (xc P ((k - 1) • Q)) = _
      rw [hKm, xc_some]
    have hAk : A k = v (xk * x₁ - (P.freyCurve⁄ℚ).a₄) := by
      show v (xc P (k • Q) * x₁ - (P.freyCurve⁄ℚ).a₄) = _
      rw [hK, xc_some]
    have hBk : B k = v (xk - x₁) := by
      show v (xc P (k • Q) - x₁) = _
      rw [hK, xc_some]
    have hExk : E (v xk) xk := E_of_v hxk0
    refine ⟨by rw [hep, hem, hAk, hBk]; linarith [hval], ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · intro hne'
      have hprod : E (v xk + v x₁) (xk * x₁) := E_mul hExk hEx₁
      rw [hek, he1] at hne' ⊢
      rcases lt_or_gt_of_ne hne' with hlt | hgt
      · rw [hAk, min_eq_left hlt.le]; exact (E_sub_I hprod (frey_E_a₄' P).I hlt).2
      · rw [hAk, min_eq_right hgt.le]; exact (I_sub_E hprod.I (frey_E_a₄' P) hgt).2
    · intro heqγ
      have hprod : I (gam P) (xk * x₁) := by
        have : v xk + v x₁ = gam P := by rw [hek, he1] at heqγ; exact heqγ
        rw [← this]; exact (E_mul hExk hEx₁).I
      rcases I_sub hprod (frey_E_a₄' P).I with h0 | h0
      · exact absurd h0 hc0
      · rw [hAk]; exact h0
    · intro hne'
      rw [hek, he1] at hne' ⊢
      rcases lt_or_gt_of_ne hne' with hlt | hgt
      · rw [hBk, min_eq_left hlt.le]; exact (E_sub_I hExk hEx₁.I hlt).2
      · rw [hBk, min_eq_right hgt.le]; exact (I_sub_E hExk.I hEx₁ hgt).2
    · intro heq'
      rw [hek, he1] at heq'
      have hI : I (v x₁) (xk - x₁) := I_sub (by rw [← heq']; exact hExk.I) hEx₁.I
      rcases hI with h0 | h0
      · exact absurd h0 hd0
      · rw [hBk, he1]; exact h0

  have hend : e (P.p - 1) = e 1 := by
    have h' : (P.p - 1) • Q + Q = 0 := by
      rw [← succ_nsmul, Nat.sub_add_cancel (by omega), ← hQ, addOrderOf_nsmul_eq_zero]
    have hneg : (P.p - 1) • Q = -Q := eq_neg_of_add_eq_zero_left h'
    rw [he1]
    show v (xc P ((P.p - 1) • Q)) = v x₁
    rw [hneg, hQdef, neg_some, xc_some]

  have hdiv : ∀ m : ℤ, 2 * gam P ∣ (P.p : ℤ) * m → 2 * gam P ∣ m := by
    have hpi : Prime (P.p : ℤ) := Nat.prime_iff_prime_int.mp hpp
    have hnd : ¬ (P.p : ℤ) ∣ 2 * gam P := by
      intro hd
      have h8 : (P.p : ℤ) ∣ 8 := by
        have : (8 : ℤ) = 2 * ((P.p : ℤ) * (padicValInt 2 P.b : ℤ)) - 2 * gam P := by
          simp only [gam]; ring
        rw [this]
        exact dvd_sub (dvd_mul_of_dvd_right (dvd_mul_right _ _) _) hd
      have h8' : P.p ∣ 8 := by exact_mod_cast h8
      have hle := Nat.le_of_dvd (by norm_num) h8'
      have hq5 := P.hp5
      have hqp := P.pp
      generalize hpg : P.p = q at h8' hle hq5 hqp
      have : q = 5 ∨ q = 6 ∨ q = 7 ∨ q = 8 := by omega
      rcases this with h | h | h | h <;> subst h
      · omega
      · omega
      · omega
      · rcases hqp.eq_one_or_self_of_dvd 2 (by norm_num) with h | h <;> omega
    intro m hm
    obtain ⟨t, ht⟩ := hm
    have hpt : (P.p : ℤ) ∣ 2 * gam P * t := ⟨m, by rw [← ht]⟩
    rcases hpi.dvd_or_dvd hpt with h | h
    · exact absurd h hnd
    · obtain ⟨t', ht'⟩ := h
      refine ⟨t', ?_⟩
      have hp0 : (P.p : ℤ) ≠ 0 := by exact_mod_cast hpp.ne_zero
      apply mul_left_cancel₀ hp0
      rw [ht, ht']; ring

  exact arith_core P.p hp5 (gam P) e A B A₁ hbd hA₁spec h2
    (fun k hk2 hkp => (pkg k hk2 hkp).2.1) (fun k hk2 hkp => (pkg k hk2 hkp).2.2)
    (fun k hk2 hkp => (pkg k hk2 hkp).1) hend hdiv

theorem freyCurve_padicValRat_two_X_pos_of_smul_eq_zero (P : FreyPackage)
    (Q : (P.freyCurve⁄ℚ).Point) (hQ : P.p • Q = 0) {x y : ℚ}
    {h : (P.freyCurve⁄ℚ).Nonsingular x y} (hxy : Q = .some x y h) :
    1 ≤ padicValRat 2 x := by
  haveI : Fact P.p.Prime := ⟨P.pp⟩
  have hne : Q ≠ 0 := by rw [hxy]; exact some_ne_zero h
  have hord : addOrderOf Q = P.p := addOrderOf_eq_prime hQ hne
  exact frey_deep_of_order Q hord hxy

end S04
p2m_reactivate "P2MW.S_FreyPackage_freyCurve_rational_p_torsion_eq_zero.S04"

theorem solution (P : FreyPackage) (y : (P.freyCurve⁄ℚ).Point) (hy : P.p • y = 0) : y = 0 :=
  S04.frey_no_rational_p_torsion P y hy

end S_FreyPackage_freyCurve_rational_p_torsion_eq_zero
end P2MW
export P2MW.S_FreyPackage_freyCurve_rational_p_torsion_eq_zero (solution)
