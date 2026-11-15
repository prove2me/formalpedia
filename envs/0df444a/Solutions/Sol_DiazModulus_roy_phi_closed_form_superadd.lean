-- Prove2me | solution 1 for DiazModulus.roy_phi_closed_form_superadd
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-14T14:16:29.064212+00:00
-- url     : https://prove2.me/submissions/a6a84d61-baf5-451a-a46c-021c5d0a31e7

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-! # Roy's closed form: one part, and superadditivity

Write `F(n, d)` for the closed form: `nd/(d − n)` if `n = 1` or `d − n = 1`, and
`(d − n)/(d − n − 1) + (n − 1)n` otherwise. For `a, δ ≥ 1` we have `F(a, a + δ) = a² − a + 1 + E(a, δ)` with the
excess `E(1, δ) = 1/δ`, `E(a, 1) = 2a − 1` (`a ≥ 2`) and `E(a, δ) = 1/(δ − 1)` (`a, δ ≥ 2`); always
`0 < E(a, δ) ≤ 2a − 1`. One part: `a(a + δ)/δ = a + a²/δ` equals `F(a, a + δ)` when `a = 1` or `δ = 1`, and
otherwise `F − a(a + δ)/δ = (aδ − a − δ)²/(δ(δ − 1)) ≥ 0`. Superadditivity: `F(a + b, ·)` is always in the second
case, and after cancelling the squares the claim becomes `E(a, δ₁) + E(b, δ₂) + 1 ≤ 2ab + 1/(δ₁ + δ₂ − 1)`.
For `a, b ≥ 2` this follows from `E ≤ 2a − 1` and `2(a − 1)(b − 1) ≥ 2`. For `a = 1` (and symmetrically `b = 1`):
if `b = 1` it is `1/δ₁ + 1/δ₂ ≤ 1 + 1/(δ₁ + δ₂ − 1)`, an equality when `δ₁ = 1` or `δ₂ = 1` and otherwise a
consequence of `1/δᵢ ≤ 1/2`; if `b ≥ 2` and `δ₂ = 1` it is an equality; if `b, δ₂ ≥ 2` the left side is at most
`3 < 2b`. -/

namespace RC4_R1a
open DiazModulus

/-- The closed form of Roy's maximum (same formula as the statement). -/
def Fq (n d : ℕ) : ℚ :=
  if n = 1 ∨ d - n = 1 then ((n : ℚ) * d) / ((d : ℚ) - n)
  else ((d : ℚ) - n) / ((d : ℚ) - n - 1) + ((n : ℚ) - 1) * n

/-- The excess of `Fq a (a + δ)` over `a² − a + 1`. -/
def E (a δ : ℕ) : ℚ := if a = 1 then 1 / (δ : ℚ) else if δ = 1 then 2 * a - 1 else 1 / ((δ : ℚ) - 1)

theorem Fq_add (a δ : ℕ) :
    Fq a (a + δ) = if a = 1 ∨ δ = 1 then (a : ℚ) * (a + δ) / δ
      else (δ : ℚ) / (δ - 1) + ((a : ℚ) - 1) * a := by
  simp only [Fq, Nat.add_sub_cancel_left, Nat.cast_add, add_sub_cancel_left]

theorem Fq_eq (a δ : ℕ) (ha : 0 < a) (hδ : 0 < δ) :
    Fq a (a + δ) = (a : ℚ) ^ 2 - a + 1 + E a δ := by
  have hδq : (δ : ℚ) ≠ 0 := by exact_mod_cast hδ.ne'
  rw [Fq_add]
  unfold E
  by_cases h1 : a = 1
  · subst h1; simp only [true_or, if_true, Nat.cast_one]; field_simp; ring
  · by_cases h2 : δ = 1
    · subst h2; simp only [h1, or_true, if_true, if_false, Nat.cast_one]; ring
    · have h2q : (δ : ℚ) - 1 ≠ 0 := by
        have : (2 : ℚ) ≤ δ := by exact_mod_cast (show 2 ≤ δ by omega)
        intro h; linarith
      simp only [h1, h2, or_self, if_false]
      field_simp
      ring

theorem E_pos_le (a δ : ℕ) (ha : 0 < a) (hδ : 0 < δ) : 0 < E a δ ∧ E a δ ≤ 2 * a - 1 := by
  have haq : (1 : ℚ) ≤ a := by exact_mod_cast ha
  have hδq : (1 : ℚ) ≤ δ := by exact_mod_cast hδ
  unfold E
  split_ifs with h1 h2
  · subst h1
    exact ⟨by positivity, by rw [div_le_iff₀ (by linarith)]; push_cast; linarith⟩
  · have : (2 : ℚ) ≤ a := by exact_mod_cast (show 2 ≤ a by omega)
    constructor <;> linarith
  · have : (2 : ℚ) ≤ δ := by exact_mod_cast (show 2 ≤ δ by omega)
    exact ⟨div_pos one_pos (by linarith), by rw [div_le_iff₀ (by linarith)]; nlinarith⟩

theorem E_big (a δ : ℕ) (ha : a ≠ 1) (hδ : δ ≠ 1) : E a δ = 1 / ((δ : ℚ) - 1) := by
  simp only [E, if_neg ha, if_neg hδ]

/-- The reduced superadditivity inequality when the first part has `a = 1`. -/
theorem core_one (δ₁ b δ₂ : ℕ) (hδ₁ : 0 < δ₁) (hb : 0 < b) (hδ₂ : 0 < δ₂) :
    E 1 δ₁ + E b δ₂ + 1 ≤ 2 * (b : ℚ) + E (1 + b) (δ₁ + δ₂) := by
  have hδ₁q : (1 : ℚ) ≤ δ₁ := by exact_mod_cast hδ₁
  have hE1 : E 1 δ₁ = 1 / (δ₁ : ℚ) := by simp [E]
  have hbig : E (1 + b) (δ₁ + δ₂) = 1 / ((δ₁ : ℚ) + δ₂ - 1) := by
    rw [E_big _ _ (by omega) (by omega)]; push_cast; ring
  have hpos : 0 < E (1 + b) (δ₁ + δ₂) := (E_pos_le _ _ (by omega) (by omega)).1
  have h1 : 1 / (δ₁ : ℚ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hδ₁q
  rw [hE1]
  by_cases hb1 : b = 1
  · subst hb1
    have hE2 : E 1 δ₂ = 1 / (δ₂ : ℚ) := by simp [E]
    rw [hE2, hbig]
    rw [hbig] at hpos
    by_cases hd1 : δ₁ = 1
    · subst hd1; push_cast; rw [show (1 : ℚ) + δ₂ - 1 = δ₂ by ring]; linarith
    · by_cases hd2 : δ₂ = 1
      · subst hd2; push_cast; rw [show (δ₁ : ℚ) + 1 - 1 = δ₁ by ring]; linarith
      · have a1 : 1 / (δ₁ : ℚ) ≤ 1 / 2 :=
          one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast (show 2 ≤ δ₁ by omega))
        have a2 : 1 / (δ₂ : ℚ) ≤ 1 / 2 :=
          one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast (show 2 ≤ δ₂ by omega))
        push_cast; linarith
  · have hb2 : (2 : ℚ) ≤ b := by exact_mod_cast (show 2 ≤ b by omega)
    by_cases hd2 : δ₂ = 1
    · subst hd2
      have hE2 : E b 1 = 2 * b - 1 := by simp [E, hb1]
      rw [hE2, hbig]; push_cast; rw [show (δ₁ : ℚ) + 1 - 1 = δ₁ by ring]; linarith
    · have hE2 : E b δ₂ ≤ 1 := by
        rw [E_big _ _ hb1 hd2, div_le_one (by
          have : (2 : ℚ) ≤ δ₂ := by exact_mod_cast (show 2 ≤ δ₂ by omega)
          linarith)]
        have : (2 : ℚ) ≤ δ₂ := by exact_mod_cast (show 2 ≤ δ₂ by omega)
        linarith
      linarith

/-- The reduced superadditivity inequality. -/
theorem core (a δ₁ b δ₂ : ℕ) (ha : 0 < a) (hδ₁ : 0 < δ₁) (hb : 0 < b) (hδ₂ : 0 < δ₂) :
    E a δ₁ + E b δ₂ + 1 ≤ 2 * (a : ℚ) * b + E (a + b) (δ₁ + δ₂) := by
  by_cases ha1 : a = 1
  · subst ha1; have := core_one δ₁ b δ₂ hδ₁ hb hδ₂; push_cast; linarith
  · by_cases hb1 : b = 1
    · subst hb1
      have := core_one δ₂ a δ₁ hδ₂ ha hδ₁
      rw [add_comm 1 a, add_comm δ₂ δ₁] at this
      push_cast; linarith
    · have ha2 : (2 : ℚ) ≤ a := by exact_mod_cast (show 2 ≤ a by omega)
      have hb2 : (2 : ℚ) ≤ b := by exact_mod_cast (show 2 ≤ b by omega)
      have e1 := (E_pos_le a δ₁ ha hδ₁).2
      have e2 := (E_pos_le b δ₂ hb hδ₂).2
      have e3 := (E_pos_le (a + b) (δ₁ + δ₂) (by omega) (by omega)).1
      nlinarith [mul_nonneg (sub_nonneg.2 ha2) (sub_nonneg.2 hb2)]

theorem L1 (a x : ℕ) (ha : 0 < a) (hax : a < x) : ((a : ℚ) * x) / ((x : ℚ) - a) ≤ Fq a x := by
  obtain ⟨δ, rfl⟩ : ∃ δ, x = a + δ := ⟨x - a, by omega⟩
  rw [Fq_add]
  push_cast
  rw [add_sub_cancel_left]
  split_ifs with h
  · exact le_rfl
  · rw [not_or] at h
    have ha2 : (2 : ℚ) ≤ a := by exact_mod_cast (show 2 ≤ a by omega)
    have hδ2 : (2 : ℚ) ≤ δ := by exact_mod_cast (show 2 ≤ δ by omega)
    have hδ0 : (δ : ℚ) ≠ 0 := by intro h; linarith
    have hδ1 : (δ : ℚ) - 1 ≠ 0 := by intro h; linarith
    have key : (δ : ℚ) / (δ - 1) + ((a : ℚ) - 1) * a - (a : ℚ) * (a + δ) / δ =
        ((a : ℚ) * δ - a - δ) ^ 2 / (δ * (δ - 1)) := by
      field_simp; ring
    have : 0 ≤ ((a : ℚ) * δ - a - δ) ^ 2 / (δ * (δ - 1)) :=
      div_nonneg (sq_nonneg _) (by nlinarith)
    linarith

theorem L2 (a x b y : ℕ) (ha : 0 < a) (hax : a < x) (hb : 0 < b) (hby : b < y) :
    Fq a x + Fq b y ≤ Fq (a + b) (x + y) := by
  obtain ⟨δ₁, rfl⟩ : ∃ δ, x = a + δ := ⟨x - a, by omega⟩
  obtain ⟨δ₂, rfl⟩ : ∃ δ, y = b + δ := ⟨y - b, by omega⟩
  rw [show a + δ₁ + (b + δ₂) = (a + b) + (δ₁ + δ₂) by ring, Fq_eq _ _ ha (by omega),
    Fq_eq _ _ hb (by omega), Fq_eq _ _ (by omega) (by omega)]
  have := core a δ₁ b δ₂ ha (by omega) hb (by omega)
  push_cast
  nlinarith

end RC4_R1a

open DiazModulus RC4_R1a in
theorem solution :
    let F : ℕ → ℕ → ℚ := fun n d =>
      if n = 1 ∨ d - n = 1 then ((n : ℚ) * d) / ((d : ℚ) - n)
      else ((d : ℚ) - n) / ((d : ℚ) - n - 1) + ((n : ℚ) - 1) * n
    (∀ a x : ℕ, 0 < a → a < x → ((a : ℚ) * x) / ((x : ℚ) - a) ≤ F a x) ∧
    ∀ a x b y : ℕ, 0 < a → a < x → 0 < b → b < y → F a x + F b y ≤ F (a + b) (x + y) := by
  intro F
  exact ⟨L1, L2⟩
