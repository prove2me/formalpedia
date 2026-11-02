-- Prove2me | solution 1 for DiazModulus.two_pow_pi_or_three_pow_pi_transcendental
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-01T09:22:08.310462+00:00
-- url     : https://prove2.me/submissions/ce1ba4f4-224f-49df-9e53-39e063b2a85c

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_five_exponentials

open Complex ComplexConjugate

/-! # `2^π` or `3^π` is transcendental

Waldschmidt 1988, statement (2.2.3), p. 379, at `t = π`, `β = i`. Apply the five exponentials theorem
to `x = (1, π)`, `y = (log 2, log 3)` and `η = i`. The five exponentials are `2`, `3`, `2^π`, `3^π` and
`e^{iπ} = -1`, so `2^π` and `3^π` cannot both be algebraic.
* `x` is `ℚ`-independent because `π` is irrational.
* `y` is `ℚ`-independent: `(p / q) log 2 = log 3` with `p, q > 0` gives `2^p = 3^q`, and `2 ∤ 3^q`. -/

open DiazModulus in
theorem solution :
    Transcendental ℚ ((2 : ℝ) ^ Real.pi) ∨ Transcendental ℚ ((3 : ℝ) ^ Real.pi) := by
  by_contra hcon
  rw [not_or, Transcendental, Transcendental, not_not, not_not] at hcon
  -- the exponentials, as complex numbers
  have hpow : ∀ a : ℝ, 0 < a → (((a ^ Real.pi : ℝ)) : ℂ) = Complex.exp (Real.pi * Real.log a) := by
    intro a ha
    rw [Real.rpow_def_of_pos ha, Complex.ofReal_exp]
    push_cast; ring_nf
  have hexp : ∀ a : ℝ, 0 < a → Complex.exp (1 * Real.log a) = (a : ℂ) := by
    intro a ha
    rw [one_mul, ← Complex.ofReal_exp, Real.exp_log ha]
  have hm1 : IsAlgebraic ℚ (-1 : ℂ) := by simpa using isAlgebraic_algebraMap (R := ℚ) (A := ℂ) (-1 : ℚ)
  have hI : IsAlgebraic ℚ Complex.I := IsAlgebraic.of_pow two_pos (by rw [Complex.I_sq]; exact hm1)
  -- `x = (1, π)` is `ℚ`-independent
  have hx : LinearIndependent ℚ ![(1 : ℂ), (Real.pi : ℂ)] := by
    rw [LinearIndependent.pair_iff' one_ne_zero]
    intro q hq
    apply irrational_pi.ne_rat q
    exact_mod_cast (by simpa [Rat.smul_def] using hq : (q : ℂ) = Real.pi).symm
  -- `y = (log 2, log 3)` is `ℚ`-independent
  have hy : LinearIndependent ℚ ![(Real.log 2 : ℂ), (Real.log 3 : ℂ)] := by
    have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
    rw [LinearIndependent.pair_iff' (by exact_mod_cast h2.ne')]
    intro q hq
    have hq' : (q : ℝ) * Real.log 2 = Real.log 3 := by
      exact_mod_cast (by simpa [Rat.smul_def] using hq : (q : ℂ) * Real.log 2 = Real.log 3)
    have qpos : 0 < q := by
      have : (0 : ℝ) < q := by nlinarith
      exact_mod_cast this
    obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = q.num := ⟨q.num.toNat, Int.toNat_of_nonneg (Rat.num_pos.mpr qpos).le⟩
    have hn0 : n ≠ 0 := by rintro rfl; exact (Rat.num_pos.mpr qpos).ne' (by simpa using hn.symm)
    have hnq : (n : ℝ) = q * q.den := by
      rw [← Int.cast_natCast, hn]; exact_mod_cast (Rat.mul_den_eq_num q).symm
    have hlog : Real.log ((2 : ℝ) ^ n) = Real.log ((3 : ℝ) ^ q.den) := by
      rw [Real.log_pow, Real.log_pow, hnq, ← hq']; ring
    have h23 : ((2 ^ n : ℕ) : ℝ) = ((3 ^ q.den : ℕ) : ℝ) := by
      push_cast
      exact Real.log_injOn_pos (Set.mem_Ioi.mpr (by positivity)) (Set.mem_Ioi.mpr (by positivity)) hlog
    have h23' : 2 ^ n = 3 ^ q.den := by exact_mod_cast h23
    have : 2 ∣ 3 ^ q.den := h23' ▸ dvd_pow_self 2 hn0
    have := Nat.prime_two.dvd_of_dvd_pow this
    omega
  refine five_exponentials ![1, (Real.pi : ℂ)] ![(Real.log 2 : ℂ), (Real.log 3 : ℂ)] Complex.I hx hy hI
    Complex.I_ne_zero ⟨?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    · rw [hexp 2 two_pos]; exact_mod_cast (isAlgebraic_algebraMap (2 : ℚ) : IsAlgebraic ℚ ((2 : ℚ) : ℂ))
    · rw [hexp 3 three_pos]; exact_mod_cast (isAlgebraic_algebraMap (3 : ℚ) : IsAlgebraic ℚ ((3 : ℚ) : ℂ))
    · rw [← hpow 2 two_pos]; exact hcon.1.algebraMap
    · rw [← hpow 3 three_pos]; exact hcon.2.algebraMap
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, div_one]
    rw [mul_comm, Complex.exp_pi_mul_I]
    exact hm1
