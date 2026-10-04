-- Prove2me | solution 1 for DiazModulus.real_axis_root_of_unity_implies_pi_sq_rat
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T05:39:07.910597+00:00
-- url     : https://prove2.me/submissions/9ffb6c19-20f0-4c96-bab4-17f8425b2b81

import Mathlib

theorem solution :
    ∀ γ : ℂ, γ.im = 0 →
      IsOfFinOrder (Complex.exp (γ / (((Real.pi : ℝ) : ℂ) * Complex.I))) →
      ∃ q : ℚ, γ = (((q : ℚ)) : ℂ) * ((((Real.pi ^ 2 : ℝ))) : ℂ) := by
  intro γ _ hfin
  obtain ⟨n, hn, hpow⟩ := (isOfFinOrder_iff_pow_eq_one).1 hfin
  rw [← Complex.exp_nat_mul, Complex.exp_eq_one_iff] at hpow
  obtain ⟨k, hk⟩ := hpow
  have hpi : ((Real.pi : ℝ) : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  refine ⟨-2 * k / n, ?_⟩
  have hγ : γ = (k * (2 * ((Real.pi : ℝ) : ℂ) * Complex.I)) / n * (((Real.pi : ℝ) : ℂ) * Complex.I) := by
    rw [← hk]; field_simp
  rw [hγ]
  push_cast
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring
