-- Prove2me | solution 1 for DiazModulus.pi_log_two_or_pi_log_three_transcendental
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-23T16:24:18.012533+00:00
-- url     : https://prove2.me/submissions/3041b359-1b99-4bfa-860b-5815afe4ff74

import Mathlib
import Theorems.Thm_Schanuel_gelfond_schneider

/-- `log 2 / log 3` is not rational: `2^d = 3^n` has no solution with `d ≥ 1`. -/
theorem pilog_ratio_not_rat : ∀ q : ℚ, (((Real.log 2 / Real.log 3 : ℝ)) : ℂ) ≠ (q : ℂ) := by
  intro q hq
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hr : Real.log 2 / Real.log 3 = (q : ℝ) := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < q := by rw [← hr]; positivity
  have hnum : 0 < q.num := Rat.num_pos.2 (by exact_mod_cast hqpos)
  set m : ℕ := q.num.toNat with hm
  have hmnum : (m : ℤ) = q.num := Int.toNat_of_nonneg hnum.le
  have hq_eq : (q : ℝ) = (m : ℝ) / (q.den : ℝ) := by
    rw [Rat.cast_def]
    congr 1
    exact_mod_cast hmnum.symm
  have hden : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
  have hlin : (q.den : ℝ) * Real.log 2 = (m : ℝ) * Real.log 3 := by
    have : Real.log 2 = (m : ℝ) / (q.den : ℝ) * Real.log 3 := by
      rw [← hq_eq, ← hr]; field_simp
    rw [this]; field_simp
  have hpow : ((2 : ℝ) ^ q.den) = (3 : ℝ) ^ m := by
    have := congrArg Real.exp hlin
    rwa [← Real.log_pow, ← Real.log_pow, Real.exp_log (by positivity),
      Real.exp_log (by positivity)] at this
  have hnat : (2 ^ q.den : ℕ) = 3 ^ m := by exact_mod_cast hpow
  have hev : Even (2 ^ q.den) := (Nat.even_pow.2 ⟨even_two, q.den_nz⟩)
  have hod : Odd (3 ^ m) := Odd.pow (by decide)
  rw [hnat] at hev
  exact (Nat.not_even_iff_odd.2 hod) hev

/-- If `π log 2` and `π log 3` were both algebraic, their quotient `log 2 / log 3` would be
algebraic, and Gelfond–Schneider with `l = log 3` would make `e^{log 2} = 2` transcendental. -/
theorem solution :
    Transcendental ℚ (Real.pi * Real.log 2) ∨ Transcendental ℚ (Real.pi * Real.log 3) := by
  by_contra h
  simp only [not_or, Transcendental, not_not] at h
  obtain ⟨h2, h3⟩ := h
  have c2 : IsAlgebraic ℚ (((Real.pi * Real.log 2 : ℝ)) : ℂ) := by
    simpa using h2.algebraMap (A := ℂ)
  have c3 : IsAlgebraic ℚ (((Real.pi * Real.log 3 : ℝ)) : ℂ) := by
    simpa using h3.algebraMap (A := ℂ)
  have hπ : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hb : IsAlgebraic ℚ (((Real.log 2 / Real.log 3 : ℝ)) : ℂ) := by
    have heq : (((Real.log 2 / Real.log 3 : ℝ)) : ℂ)
        = (((Real.pi * Real.log 2 : ℝ)) : ℂ) / (((Real.pi * Real.log 3 : ℝ)) : ℂ) := by
      push_cast
      have : ((Real.pi : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hπ
      have : ((Real.log 3 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hl3.ne'
      field_simp
    rw [heq]
    rw [← mem_algebraicClosure_iff (F := ℚ)] at c2 c3 ⊢
    exact div_mem c2 c3
  have hl : IsAlgebraic ℚ (Complex.exp (((Real.log 3 : ℝ)) : ℂ)) := by
    rw [← Complex.ofReal_exp, Real.exp_log (by norm_num)]
    simpa using (isAlgebraic_algebraMap (3 : ℚ) : IsAlgebraic ℚ (algebraMap ℚ ℂ 3))
  have hl0 : (((Real.log 3 : ℝ)) : ℂ) ≠ 0 := by exact_mod_cast hl3.ne'
  have hGS := Schanuel.gelfond_schneider _ _ hb pilog_ratio_not_rat hl hl0
  have hprod : (((Real.log 2 / Real.log 3 : ℝ)) : ℂ) * (((Real.log 3 : ℝ)) : ℂ)
      = (((Real.log 2 : ℝ)) : ℂ) := by
    push_cast
    field_simp
  rw [hprod, ← Complex.ofReal_exp, Real.exp_log (by norm_num)] at hGS
  exact hGS (by simpa using (isAlgebraic_algebraMap (2 : ℚ) : IsAlgebraic ℚ (algebraMap ℚ ℂ 2)))

#print axioms solution
