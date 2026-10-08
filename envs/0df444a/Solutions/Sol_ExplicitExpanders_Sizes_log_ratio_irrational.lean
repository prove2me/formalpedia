-- Prove2me | solution 1 for ExplicitExpanders.Sizes.log_ratio_irrational
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T22:13:48.298905+00:00
-- url     : https://prove2.me/submissions/6d94311e-e816-431a-a53b-70a7cd2ba2da

import Mathlib

theorem solution {q₁ q₂ : ℕ} (hq₁ : q₁.Prime) (hq₂ : q₂.Prime) (hne : q₁ ≠ q₂) :
    Irrational (Real.log q₁ / Real.log q₂) := by
  rintro ⟨r, hr⟩
  have h1 : (0 : ℝ) < Real.log q₁ :=
    Real.log_pos (by exact_mod_cast hq₁.one_lt)
  have h2 : (0 : ℝ) < Real.log q₂ :=
    Real.log_pos (by exact_mod_cast hq₂.one_lt)
  have hrpos : (0 : ℝ) < r := by rw [hr]; exact div_pos h1 h2
  have hrq : (0 : ℚ) < r := by exact_mod_cast hrpos
  have hnum : 0 < r.num := Rat.num_pos.mpr hrq
  obtain ⟨n, hn⟩ : ∃ n : ℕ, r.num = n := ⟨r.num.toNat, (Int.toNat_of_nonneg hnum.le).symm⟩
  have hden : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
  have hcast : (r : ℝ) = (n : ℝ) / r.den := by
    rw [Rat.cast_def, hn]
    push_cast
    rfl
  have key : (r.den : ℝ) * Real.log q₁ = n * Real.log q₂ := by
    have := hr
    rw [hcast] at this
    field_simp at this
    linarith
  have hpow : ((q₁ ^ r.den : ℕ) : ℝ) = ((q₂ ^ n : ℕ) : ℝ) := by
    have e1 : Real.log ((q₁ : ℝ) ^ r.den) = Real.log ((q₂ : ℝ) ^ n) := by
      rw [Real.log_pow, Real.log_pow]; exact key
    have p1 : (0 : ℝ) < (q₁ : ℝ) ^ r.den := by
      have : (0 : ℝ) < q₁ := by exact_mod_cast hq₁.pos
      positivity
    have p2 : (0 : ℝ) < (q₂ : ℝ) ^ n := by
      have : (0 : ℝ) < q₂ := by exact_mod_cast hq₂.pos
      positivity
    push_cast
    exact Real.log_injOn_pos p1 p2 e1
  have hnat : q₁ ^ r.den = q₂ ^ n := by exact_mod_cast hpow
  have hdvd : q₁ ∣ q₂ ^ n := by
    rw [← hnat]; exact dvd_pow_self q₁ r.den_pos.ne'
  have := (Nat.prime_dvd_prime_iff_eq hq₁ hq₂).mp (hq₁.dvd_of_dvd_pow hdvd)
  exact hne this
