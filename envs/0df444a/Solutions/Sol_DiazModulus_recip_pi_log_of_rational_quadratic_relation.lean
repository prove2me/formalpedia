-- Prove2me | solution 1 for DiazModulus.recip_pi_log_of_rational_quadratic_relation
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-04T18:55:47.851578+00:00
-- url     : https://prove2.me/submissions/9c1f719e-9a8e-4016-ac7a-c47a88a67821

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_four_exponentials_trdeg_one
import Theorems.Thm_Transcendence_trdeg_adjoin_le_one_of_isAlgebraic_adjoin

open Complex ComplexConjugate

/-- Brownawell's route (1974, Cor. 5). Suppose `e^{iγ/π}` algebraic; then so is `e^{iq/π}` for
every rational `q`. From `a t² + b π² = c`,
`t²/(iπ) = (-c/(aγ)) · (iγ/π) + (b/a) · (iπ)` is a logarithm of an algebraic number, and `t` is
algebraic over `ℚ[π]`. The matrix `[[t, t²/(iπ)], [iπ, t]]` has rank one, logarithmic entries and
transcendence degree one, so by `four_exponentials_trdeg_one` its rows or columns are
`ℚ`-dependent; that forces a relation `α t + β iπ = 0`, impossible since `t` is real and non-zero.
The cases `b = 0` and `c = 0` need no separate treatment. -/
theorem solution (t : ℝ) (ht : t ≠ 0)
    (he : IsAlgebraic ℚ (Complex.exp (t : ℂ))) (a b c : ℚ) (ha : a ≠ 0)
    (hrel : (a : ℝ) * t ^ 2 + (b : ℝ) * Real.pi ^ 2 = (c : ℝ))
    (γ : ℚ) (hγ : γ ≠ 0) :
    Transcendental ℚ (Complex.exp (Complex.I * (γ : ℂ) / ((Real.pi : ℝ) : ℂ))) := by
  intro hw
  set P : ℂ := ((Real.pi : ℝ) : ℂ) with hPdef
  set T : ℂ := (t : ℂ) with hTdef
  have hP0 : P ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  have hT0 : T ≠ 0 := Complex.ofReal_ne_zero.2 ht
  have hIP0 : Complex.I * P ≠ 0 := mul_ne_zero Complex.I_ne_zero hP0
  have hrelC : (a : ℂ) * T ^ 2 + (b : ℂ) * P ^ 2 = (c : ℂ) := by
    have := congrArg (fun x : ℝ => (x : ℂ)) hrel
    push_cast at this
    exact this
  -- rational multiples of logarithms of algebraic numbers are logarithms of algebraic numbers
  have hq : ∀ z : ℂ, IsAlgebraic ℚ (Complex.exp z) → ∀ q : ℚ,
      IsAlgebraic ℚ (Complex.exp ((q : ℂ) * z)) := by
    intro z hz q
    have hqd : (q.den : ℂ) * (q : ℂ) = (q.num : ℂ) := by
      exact_mod_cast (mul_comm _ _).trans (Rat.mul_den_eq_num q)
    refine IsAlgebraic.of_pow q.den_pos ?_
    rw [← Complex.exp_nat_mul, ← mul_assoc, hqd, Complex.exp_int_mul]
    rcases Int.eq_nat_or_neg q.num with ⟨m, hm | hm⟩ <;> rw [hm]
    · rw [zpow_natCast]; exact hz.pow m
    · rw [zpow_neg, zpow_natCast]; exact (hz.pow m).inv
  have hπI : IsAlgebraic ℚ (Complex.exp (Complex.I * P)) := by
    rw [mul_comm, Complex.exp_pi_mul_I]
    exact isAlgebraic_one.neg
  -- `t² / (iπ) = (-c/(aγ)) · (iγ/π) + (b/a) · (iπ)` is a logarithm of an algebraic number
  have hid : T ^ 2 / (Complex.I * P) = ((-c / (a * γ) : ℚ) : ℂ) * (Complex.I * (γ : ℂ) / P) +
      ((b / a : ℚ) : ℂ) * (Complex.I * P) := by
    rw [div_eq_iff hIP0]
    push_cast
    field_simp
    linear_combination hrelC + ((c : ℂ) - P ^ 2 * (b : ℂ)) * Complex.I_sq
  have hL : IsAlgebraic ℚ (Complex.exp (T ^ 2 / (Complex.I * P))) := by
    rw [hid, Complex.exp_add]
    exact (hq _ hw _).mul (hq _ hπI _)
  -- the four numbers are algebraic over `ℚ[π]`, so they generate transcendence degree one
  have lift : ∀ z : ℂ, IsAlgebraic ℚ z → IsAlgebraic ↥(Algebra.adjoin ℚ ({P} : Set ℂ)) z :=
    fun z hz => hz.extendScalars (algebraMap ℚ _).injective
  have hPA : IsAlgebraic ↥(Algebra.adjoin ℚ ({P} : Set ℂ)) P :=
    isAlgebraic_algebraMap
      (⟨P, Algebra.self_mem_adjoin_singleton ℚ P⟩ : Algebra.adjoin ℚ ({P} : Set ℂ))
  have hIPA : IsAlgebraic ↥(Algebra.adjoin ℚ ({P} : Set ℂ)) (Complex.I * P) :=
    (lift _ (IsAlgebraic.of_pow two_pos (by rw [Complex.I_sq]; exact isAlgebraic_one.neg))).mul
      hPA
  have hTA : IsAlgebraic ↥(Algebra.adjoin ℚ ({P} : Set ℂ)) T := by
    refine IsAlgebraic.of_pow two_pos ?_
    rw [show T ^ 2 = ((c / a : ℚ) : ℂ) - ((b / a : ℚ) : ℂ) * P ^ 2 by
      push_cast; field_simp; linear_combination hrelC]
    exact (lift _ (isAlgebraic_ratCast ℚ _)).sub ((lift _ (isAlgebraic_ratCast ℚ _)).mul
      (hPA.pow 2))
  have htr := Transcendence.trdeg_adjoin_le_one_of_isAlgebraic_adjoin P
    ({T, T ^ 2 / (Complex.I * P), Complex.I * P, T} : Set ℂ) (by
      intro s hs
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
      rcases hs with rfl | rfl | rfl | rfl
      · exact hTA
      · rw [div_eq_mul_inv]; exact (hTA.pow 2).mul hIPA.inv
      · exact hIPA
      · exact hTA)
  -- `α t + β iπ = 0` forces `β = 0` (imaginary part), then `α = 0`
  have key : ∀ α β : ℚ, ¬(α = 0 ∧ β = 0) →
      (α : ℂ) * T + (β : ℂ) * (Complex.I * P) = 0 → False := by
    intro α β hab h
    have hβ : β = 0 := by simpa [hTdef, hPdef, Real.pi_ne_zero] using congrArg Complex.im h
    subst hβ
    exact hab ⟨by simpa [hT0] using h, rfl⟩
  -- four exponentials in transcendence degree one on `[[t, t²/(iπ)], [iπ, t]]`
  rcases DiazModulus.four_exponentials_trdeg_one T (T ^ 2 / (Complex.I * P)) (Complex.I * P) T
      he hL hπI he hT0 (div_ne_zero (pow_ne_zero 2 hT0) hIP0) hIP0 hT0
      (by rw [div_mul_cancel₀ _ hIP0]; ring) htr with
    ⟨α, β, hab, h1, -⟩ | ⟨α, β, hab, -, h2⟩
  · exact key α β hab h1
  · exact key β α (fun h => hab h.symm) (by linear_combination h2)

#print axioms solution
