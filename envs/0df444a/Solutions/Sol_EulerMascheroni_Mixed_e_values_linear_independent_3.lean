-- Prove2me | solution 3 for EulerMascheroni.Mixed.e_values_linear_independent
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-25T17:43:26.951529+00:00
-- url     : https://prove2.me/submissions/5446cef0-7858-412a-a2a2-a280ddda5825
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_eulerMascheroni_mixedCover
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_hermite_lindemann_holds
import Theorems.Thm_EulerMascheroni_Mixed_expEin_one_not_mem_exp_span

theorem solution (a b c : ℝ) (ha : IsAlgebraic ℚ a) (hb : IsAlgebraic ℚ b)
    (hc : IsAlgebraic ℚ c)
    (h : (a : ℂ) + (b : ℂ) * Complex.exp 1 +
      (c : ℂ) * EulerMascheroni.Mixed.expEin 1 = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  have hC : ∀ x : ℝ, IsAlgebraic ℚ x → IsAlgebraic ℚ (x : ℂ) := fun x hx =>
    hx.algebraMap (A := ℂ)
  by_cases hc0 : c = 0
  · subst hc0
    simp only [Complex.ofReal_zero, zero_mul, add_zero] at h
    have hb0 : b = 0 := by
      by_contra hb0
      have hbC : (b : ℂ) ≠ 0 := by exact_mod_cast hb0
      have he : Complex.exp 1 = -(a : ℂ) / (b : ℂ) := by
        field_simp
        linear_combination h
      have halg : IsAlgebraic ℚ (Complex.exp 1) := by
        rw [he, div_eq_mul_inv]
        exact ((hC a ha).neg).mul (hC b hb).inv
      exact DiazModulus.hermite_lindemann_holds 1 one_ne_zero isAlgebraic_one halg
    subst hb0
    simp only [Complex.ofReal_zero, zero_mul, add_zero] at h
    exact ⟨by exact_mod_cast h, rfl, rfl⟩
  · exfalso
    have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc0
    apply EulerMascheroni.Mixed.expEin_one_not_mem_exp_span (-a / c) (-b / c)
      (by rw [div_eq_mul_inv]; exact ha.neg.mul hc.inv)
      (by rw [div_eq_mul_inv]; exact hb.neg.mul hc.inv)
    push_cast
    field_simp
    linear_combination h
