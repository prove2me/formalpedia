-- Prove2me | solution 1 for BinaryQuadraticForm.card_automorphs
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-25T09:16:24.109693+00:00
-- url     : https://prove2.me/submissions/59f90cd9-dafa-4daf-aec0-40a6ba30917c

import Mathlib
import Definitions.Def_RPLib_S3_HurwitzA

set_option autoImplicit false

namespace UploadSW44

open RamanujanPetersson.Hurwitz

/-- Textbook reducedness (`|b| ≤ a ≤ c`, `b ≥ 0` on the boundary) with `a ≠ 0` gives the library's
`IsReduced`. -/
theorem isReduced_of_tb {a b c : ℤ} (ha : a ≠ 0)
    (h : |b| ≤ a ∧ a ≤ c ∧ (|b| = a ∨ a = c → 0 ≤ b)) : (⟨a, b, c⟩ : BQF).IsReduced := by
  obtain ⟨h1, h2, h3⟩ := h
  have hb := abs_le.1 h1
  have ha0 : 0 ≤ a := le_trans (abs_nonneg b) h1
  show -a < b ∧ b ≤ a ∧ a ≤ c ∧ (a = c → 0 ≤ b)
  refine ⟨?_, hb.2, h2, fun hac => h3 (Or.inr hac)⟩
  by_contra hcon
  have hbeq : b = -a := by omega
  have habs : |b| = a := by rw [hbeq, abs_neg, abs_of_nonneg ha0]
  have := h3 (Or.inl habs)
  omega

/-- The pointwise automorph condition is `act γ f = f`. -/
theorem forall_iff_act (f : BQF) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    (∀ x y : ℤ, f.a * (γ 0 0 * x + γ 0 1 * y) ^ 2 +
          f.b * (γ 0 0 * x + γ 0 1 * y) * (γ 1 0 * x + γ 1 1 * y) +
          f.c * (γ 1 0 * x + γ 1 1 * y) ^ 2 = f.a * x ^ 2 + f.b * x * y + f.c * y ^ 2) ↔
      act γ f = f := by
  constructor
  · intro h
    have e : ∀ x y : ℤ, (act γ f).eval x y = f.eval x y := by
      intro x y; rw [eval_act]; exact h x y
    have h10 := e 1 0
    have h01 := e 0 1
    have h11 := e 1 1
    simp only [BQF.eval] at h10 h01 h11
    norm_num at h10 h01 h11
    refine BQF.ext ?_ ?_ ?_ <;> linarith
  · intro h x y
    have e := eval_act γ f x y
    rw [h] at e
    exact e.symm

/-- On a reduced form, the two special discriminants pick out `[g, 0, g]` and `[g, g, g]`. -/
theorem key (r : BQF) (hr : r.IsReduced) :
    (r.disc = -4 * (r.content : ℤ) ^ 2 ↔ r.b = 0 ∧ r.a = r.c) ∧
      (r.disc = -3 * (r.content : ℤ) ^ 2 ↔ r.a = r.b ∧ r.b = r.c) := by
  have ha := hr.a_pos
  obtain ⟨h1, h2, h3, h4⟩ := hr
  obtain ⟨a', ha'⟩ := r.content_dvd_a
  obtain ⟨b', hb'⟩ := r.content_dvd_b
  obtain ⟨c', hc'⟩ := r.content_dvd_c
  have hdisc : r.disc = r.b ^ 2 - 4 * r.a * r.c := rfl
  obtain ⟨a, b, c⟩ := r
  simp only at ha h1 h2 h3 h4 ha' hb' hc' hdisc ⊢
  generalize hg : ((BQF.content ⟨a, b, c⟩ : ℕ) : ℤ) = g at ha' hb' hc' ⊢
  have hg0 : 0 ≤ g := by rw [← hg]; positivity
  have hgpos : 0 < g := by
    rcases hg0.lt_or_eq with h | h
    · exact h
    · subst ha'; rw [← h] at ha; simp at ha
  subst ha' hb' hc'
  have ha1 : 0 < a' := pos_of_mul_pos_right ha hg0
  have hb1 : -a' < b' := by nlinarith
  have hb2 : b' ≤ a' := by nlinarith
  have hc1 : a' ≤ c' := by nlinarith
  have hgsq : 0 < g ^ 2 := by positivity
  rw [hdisc]
  constructor
  · constructor
    · intro h
      have h' : b' ^ 2 - 4 * a' * c' = -4 := by
        have : g ^ 2 * (b' ^ 2 - 4 * a' * c') = g ^ 2 * (-4) := by linear_combination h
        exact mul_left_cancel₀ hgsq.ne' this
      have hbsq : b' ^ 2 ≤ a' ^ 2 := by nlinarith
      have hac : a' * a' ≤ a' * c' := by nlinarith
      have ha'1 : a' = 1 := by nlinarith
      subst ha'1
      have hb' : b' = 0 ∨ b' = 1 := by omega
      rcases hb' with rfl | rfl
      · have : c' = 1 := by nlinarith
        subst this; simp
      · exfalso; omega
    · rintro ⟨hb0, hac⟩
      have hb0' : b' = 0 := by
        rcases mul_eq_zero.1 hb0 with h | h
        · omega
        · exact h
      have hac' : a' = c' := mul_left_cancel₀ hgpos.ne' hac
      subst hb0' hac'
      -- `g` is the gcd of `g a', 0, g a'`, so `a' = 1`
      have hdvd : ((g * a').toNat : ℤ) ∣ g := by
        have h0 : (((g * a').toNat : ℕ) : ℕ) ∣ BQF.content ⟨g * a', g * 0, g * a'⟩ :=
          BQF.dvd_content _ (by rw [Int.toNat_of_nonneg (by positivity)])
            (by rw [Int.toNat_of_nonneg (by positivity)]; simp)
            (by rw [Int.toNat_of_nonneg (by positivity)])
        have h1 : (((g * a').toNat : ℕ) : ℤ) ∣ ((BQF.content ⟨g * a', g * 0, g * a'⟩ : ℕ) : ℤ) :=
          Int.natCast_dvd_natCast.2 h0
        rwa [hg] at h1
      rw [Int.toNat_of_nonneg (by positivity)] at hdvd
      have hle := Int.le_of_dvd hgpos hdvd
      have : a' = 1 := by nlinarith
      subst this; ring
  · constructor
    · intro h
      have h' : b' ^ 2 - 4 * a' * c' = -3 := by
        have : g ^ 2 * (b' ^ 2 - 4 * a' * c') = g ^ 2 * (-3) := by linear_combination h
        exact mul_left_cancel₀ hgsq.ne' this
      have hbsq : b' ^ 2 ≤ a' ^ 2 := by nlinarith
      have hac : a' * a' ≤ a' * c' := by nlinarith
      have ha'1 : a' = 1 := by nlinarith
      subst ha'1
      have hb' : b' = 0 ∨ b' = 1 := by omega
      rcases hb' with rfl | rfl
      · exfalso; omega
      · have : c' = 1 := by nlinarith
        subst this; simp
    · rintro ⟨hab, hbc⟩
      have hab' : a' = b' := mul_left_cancel₀ hgpos.ne' hab
      have hbc' : b' = c' := mul_left_cancel₀ hgpos.ne' hbc
      subst hab' hbc'
      have hdvd : ((g * a').toNat : ℤ) ∣ g := by
        have h0 : (((g * a').toNat : ℕ) : ℕ) ∣ BQF.content ⟨g * a', g * a', g * a'⟩ :=
          BQF.dvd_content _ (by rw [Int.toNat_of_nonneg (by positivity)])
            (by rw [Int.toNat_of_nonneg (by positivity)])
            (by rw [Int.toNat_of_nonneg (by positivity)])
        have h1 : (((g * a').toNat : ℕ) : ℤ) ∣ ((BQF.content ⟨g * a', g * a', g * a'⟩ : ℕ) : ℤ) :=
          Int.natCast_dvd_natCast.2 h0
        rwa [hg] at h1
      rw [Int.toNat_of_nonneg (by positivity)] at hdvd
      have hle := Int.le_of_dvd hgpos hdvd
      have : a' = 1 := by nlinarith
      subst this; ring

theorem main (a b c : ℤ) (ha : 0 < a) (hdisc : b ^ 2 - 4 * a * c < 0) :
    Nat.card {γ : Matrix.SpecialLinearGroup (Fin 2) ℤ // ∀ x y : ℤ,
        a * (γ 0 0 * x + γ 0 1 * y) ^ 2 +
            b * (γ 0 0 * x + γ 0 1 * y) * (γ 1 0 * x + γ 1 1 * y) +
            c * (γ 1 0 * x + γ 1 1 * y) ^ 2 =
          a * x ^ 2 + b * x * y + c * y ^ 2} =
        (if b ^ 2 - 4 * a * c = -4 * (Int.gcd a (Int.gcd b c) : ℤ) ^ 2 then 4
        else if b ^ 2 - 4 * a * c = -3 * (Int.gcd a (Int.gcd b c) : ℤ) ^ 2 then 6
        else 2) ∧
      ((|b| ≤ a ∧ a ≤ c ∧ (|b| = a ∨ a = c → 0 ≤ b)) →
        ((b ^ 2 - 4 * a * c = -4 * (Int.gcd a (Int.gcd b c) : ℤ) ^ 2 ↔ b = 0 ∧ a = c) ∧
          (b ^ 2 - 4 * a * c = -3 * (Int.gcd a (Int.gcd b c) : ℤ) ^ 2 ↔ a = b ∧ b = c))) := by
  have hf : (⟨a, b, c⟩ : BQF).PosDef := ⟨ha, hdisc⟩
  refine ⟨?_, fun htb => key ⟨a, b, c⟩ (isReduced_of_tb ha.ne' htb)⟩
  have hcard : Nat.card {γ : Matrix.SpecialLinearGroup (Fin 2) ℤ // ∀ x y : ℤ,
        a * (γ 0 0 * x + γ 0 1 * y) ^ 2 +
            b * (γ 0 0 * x + γ 0 1 * y) * (γ 1 0 * x + γ 1 1 * y) +
            c * (γ 1 0 * x + γ 1 1 * y) ^ 2 =
          a * x ^ 2 + b * x * y + c * y ^ 2} =
      Nat.card (MulAction.stabilizer (Matrix.SpecialLinearGroup (Fin 2) ℤ) (⟨a, b, c⟩ : BQF)) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun γ =>
      (forall_iff_act ⟨a, b, c⟩ γ).trans (mem_stabilizer_iff_act γ ⟨a, b, c⟩).symm)
  obtain ⟨γ, hγ⟩ := exists_act_isReduced _ hf
  have k := key _ hγ
  rw [disc_act, content_act] at k
  have e4 : (b ^ 2 - 4 * a * c = -4 * (Int.gcd a (Int.gcd b c) : ℤ) ^ 2) ↔
      (act γ ⟨a, b, c⟩).b = 0 ∧ (act γ ⟨a, b, c⟩).a = (act γ ⟨a, b, c⟩).c := k.1
  have e3 : (b ^ 2 - 4 * a * c = -3 * (Int.gcd a (Int.gcd b c) : ℤ) ^ 2) ↔
      (act γ ⟨a, b, c⟩).a = (act γ ⟨a, b, c⟩).b ∧ (act γ ⟨a, b, c⟩).b = (act γ ⟨a, b, c⟩).c := k.2
  rw [hcard, ← card_stabilizer_act γ, card_stabilizer_of_isReduced hγ]
  simp only [e4, e3]

end UploadSW44

theorem solution (a b c : ℤ) (ha : 0 < a)
    (hdisc : b ^ 2 - 4 * a * c < 0) :
    Nat.card {γ : Matrix.SpecialLinearGroup (Fin 2) ℤ // ∀ x y : ℤ,
        a * (γ 0 0 * x + γ 0 1 * y) ^ 2 +
            b * (γ 0 0 * x + γ 0 1 * y) * (γ 1 0 * x + γ 1 1 * y) +
            c * (γ 1 0 * x + γ 1 1 * y) ^ 2 =
          a * x ^ 2 + b * x * y + c * y ^ 2} =
        (if b ^ 2 - 4 * a * c = -4 * (Int.gcd a (Int.gcd b c) : ℤ) ^ 2 then 4
        else if b ^ 2 - 4 * a * c = -3 * (Int.gcd a (Int.gcd b c) : ℤ) ^ 2 then 6
        else 2) ∧
      ((|b| ≤ a ∧ a ≤ c ∧ (|b| = a ∨ a = c → 0 ≤ b)) →
        ((b ^ 2 - 4 * a * c = -4 * (Int.gcd a (Int.gcd b c) : ℤ) ^ 2 ↔ b = 0 ∧ a = c) ∧
          (b ^ 2 - 4 * a * c = -3 * (Int.gcd a (Int.gcd b c) : ℤ) ^ 2 ↔ a = b ∧ b = c))) := by
  exact UploadSW44.main a b c ha hdisc
