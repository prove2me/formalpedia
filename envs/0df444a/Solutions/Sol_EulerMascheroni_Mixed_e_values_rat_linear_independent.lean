-- Prove2me | solution 1 for EulerMascheroni.Mixed.e_values_rat_linear_independent
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-25T17:43:27.624995+00:00
-- url     : https://prove2.me/submissions/684a0eaf-477a-4700-8298-cad2f3e04d1c

import Definitions.Def_eulerMascheroni_mixedCover
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_hermite_lindemann_holds
import Theorems.Thm_EulerMascheroni_Mixed_expEin_one_not_mem_rat_exp_span

theorem solution (a b c : ℚ)
    (h : (a : ℂ) + (b : ℂ) * Complex.exp 1 +
      (c : ℂ) * EulerMascheroni.Mixed.expEin 1 = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  by_cases hc0 : c = 0
  · subst hc0
    simp only [Rat.cast_zero, zero_mul, add_zero] at h
    have hb0 : b = 0 := by
      by_contra hb0
      have hbC : (b : ℂ) ≠ 0 := by exact_mod_cast hb0
      have he : Complex.exp 1 = ((-a / b : ℚ) : ℂ) := by
        push_cast
        field_simp
        linear_combination h
      have halg : IsAlgebraic ℚ (Complex.exp 1) := by
        rw [he]
        exact isAlgebraic_algebraMap (R := ℚ) (A := ℂ) (-a / b)
      exact DiazModulus.hermite_lindemann_holds 1 one_ne_zero isAlgebraic_one halg
    subst hb0
    simp only [Rat.cast_zero, zero_mul, add_zero] at h
    exact ⟨by exact_mod_cast h, rfl, rfl⟩
  · exfalso
    have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc0
    apply EulerMascheroni.Mixed.expEin_one_not_mem_rat_exp_span (-a / c) (-b / c)
    push_cast
    field_simp
    linear_combination h
