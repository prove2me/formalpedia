-- Prove2me | solution 1 for Erdos287.distinguished_factor_preserves_two_sieve_caps
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T19:02:54.177032+00:00
-- url     : https://prove2.me/submissions/d6442c8c-1cd8-4057-8d12-8a3dc730a34b

import Mathlib

set_option autoImplicit false

private theorem convolution_witness (f g : ArithmeticFunction ℝ) (n : ℕ)
    (hn : (f * g) n ≠ 0) : ∃ a b : ℕ, a * b = n ∧ f a ≠ 0 ∧ g b ≠ 0 := by
  rw [ArithmeticFunction.mul_apply] at hn
  obtain ⟨⟨a, b⟩, hab, h⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
  exact ⟨a, b, (Nat.mem_divisorsAntidiagonal.mp hab).1,
    fun hz => h (by simp [hz]), fun hz => h (by simp [hz])⟩

private theorem convolution_cap (f g : ArithmeticFunction ℝ) (U V : ℝ) (hU : 0 ≤ U)
    (hf : ∀ i : ℕ, f i ≠ 0 → (i : ℝ) ≤ U) (hg : ∀ i : ℕ, g i ≠ 0 → (i : ℝ) ≤ V)
    (n : ℕ) (hn : (f * g) n ≠ 0) : (n : ℝ) ≤ U * V := by
  obtain ⟨a, b, rfl, ha, hb⟩ := convolution_witness f g n hn
  rw [Nat.cast_mul]
  exact mul_le_mul (hf a ha) (hg b hb) (Nat.cast_nonneg b) hU

/-- Attach a factor of size at most `P` to a factorable sieve weight of
level `D / P`. At level `D ≥ P²` either cap can accommodate the factor,
and the prime-factor restriction on the second side is preserved. -/
theorem solution (D P A B : ℝ) (Z : ℕ) (hP : 1 ≤ P) (hA : 1 ≤ A) (hB : 1 ≤ B)
    (hAB : A * B = D) (hPD : P ^ 2 ≤ D) (p w : ArithmeticFunction ℝ)
    (hp : ∀ n : ℕ, p n ≠ 0 → (n : ℝ) ≤ P)
    (hpZ : ∀ n : ℕ, p n ≠ 0 → ∀ q : ℕ, q.Prime → q ∣ n → Z ≤ q)
    (hw : ∀ U V : ℝ, 1 ≤ U → 1 ≤ V → U * V = D / P →
      ∃ f g : ArithmeticFunction ℝ, w = f * g ∧
        (∀ n : ℕ, f n ≠ 0 → (n : ℝ) ≤ U) ∧ (∀ n : ℕ, g n ≠ 0 → (n : ℝ) ≤ V) ∧
        (∀ n : ℕ, g n ≠ 0 → ∀ q : ℕ, q.Prime → q ∣ n → Z ≤ q)) :
    ∃ f g : ArithmeticFunction ℝ, p * w = f * g ∧
      (∀ n : ℕ, f n ≠ 0 → (n : ℝ) ≤ A) ∧ (∀ n : ℕ, g n ≠ 0 → (n : ℝ) ≤ B) ∧
      (∀ n : ℕ, g n ≠ 0 → ∀ q : ℕ, q.Prime → q ∣ n → Z ≤ q) := by
  have hPpos : 0 < P := by linarith
  by_cases hPA : P ≤ A
  · have hA' : 1 ≤ A / P := (le_div_iff₀ hPpos).2 (by simpa using hPA)
    have hsplit : A / P * B = D / P := by rw [div_mul_eq_mul_div, hAB]
    obtain ⟨f, g, he, hf, hg, hgZ⟩ := hw (A / P) B hA' hB hsplit
    refine ⟨p * f, g, by rw [he, mul_assoc], ?_, hg, hgZ⟩
    intro n hn
    simpa only [mul_div_cancel₀ _ hPpos.ne'] using
      convolution_cap p f P (A / P) hPpos.le hp hf n hn
  · have hPB : P ≤ B := by
      by_contra! hsmall
      have hlt : A * B < P ^ 2 := by
        rw [pow_two]
        exact (mul_le_mul_of_nonneg_right (le_of_lt (lt_of_not_ge hPA)) (by linarith : 0 ≤ B)).trans_lt
          (mul_lt_mul_of_pos_left hsmall hPpos)
      exact (not_lt_of_ge hPD) (hAB ▸ hlt)
    have hB' : 1 ≤ B / P := (le_div_iff₀ hPpos).2 (by simpa using hPB)
    have hsplit : A * (B / P) = D / P := by rw [← mul_div_assoc, hAB]
    obtain ⟨f, g, he, hf, hg, hgZ⟩ := hw A (B / P) hA hB' hsplit
    refine ⟨f, p * g, ?_, hf, ?_, ?_⟩
    · rw [he]
      ac_rfl
    · intro n hn
      simpa only [mul_div_cancel₀ _ hPpos.ne'] using
        convolution_cap p g P (B / P) hPpos.le hp hg n hn
    · intro n hn q hq hdiv
      obtain ⟨a, b, rfl, ha, hb⟩ := convolution_witness p g n hn
      exact (hq.dvd_mul.mp hdiv).elim (hpZ a ha q hq) (hgZ b hb q hq)

