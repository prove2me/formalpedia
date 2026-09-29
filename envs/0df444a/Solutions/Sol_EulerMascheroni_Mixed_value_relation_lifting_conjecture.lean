-- Prove2me | solution 1 for EulerMascheroni.Mixed.value_relation_lifting_conjecture
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-11T13:21:38.025241+00:00
-- url     : https://prove2.me/submissions/daf03431-ff55-41b8-8ae7-a83b6365d69b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_EulerMascheroni_Mixed_e_values_linear_independent
import Theorems.Thm_EulerMascheroni_Mixed_local_intersection_algebraicity_conjecture
import Theorems.Thm_EulerMascheroni_Arithmetic_gompertz_transcendental
set_option autoImplicit false

open EulerMascheroni.Mixed

theorem solution
    (a b c d : ℝ)
    (ha : IsAlgebraic ℚ a) (hb : IsAlgebraic ℚ b)
    (hc : IsAlgebraic ℚ c) (hd : IsAlgebraic ℚ d)
    (h : (a : ℂ) + (b : ℂ) * Complex.exp 1 +
      (c : ℂ) * EulerMascheroni.Mixed.expEin 1 +
      (d : ℂ) * EulerMascheroni.Mixed.kernelOnCover 0 = 0) :
    ∃ P Q R S : Polynomial ℂ,
      P.eval 1 = (a : ℂ) ∧ Q.eval 1 = (b : ℂ) ∧
      R.eval 1 = (c : ℂ) ∧ S.eval 1 = (d : ℂ) ∧
      ∀ t : ℂ,
        P.eval (Complex.exp t) + Q.eval (Complex.exp t) * Complex.exp (Complex.exp t) +
        R.eval (Complex.exp t) * EulerMascheroni.Mixed.expEin (Complex.exp t) +
        S.eval (Complex.exp t) * EulerMascheroni.Mixed.kernelOnCover t = 0 := by
  have hk : kernelOnCover 0 = (EulerMascheroni.gompertzConstant : ℂ) := by
    simp only [kernelOnCover, Complex.exp_zero, sub_self, zero_add, sub_zero]
    field_simp
  rw [hk] at h
  have hd0 : d = 0 := by
    by_contra hd0
    have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd0
    have hrel : (EulerMascheroni.gompertzConstant : ℂ) =
        ((-a / d : ℝ) : ℂ) + ((-b / d : ℝ) : ℂ) * Complex.exp 1 +
        ((-c / d : ℝ) : ℂ) * expEin 1 := by
      push_cast
      field_simp [hdC]
      linear_combination h
    have halg := local_intersection_algebraicity_conjecture (-a/d) (-b/d) (-c/d)
      (by simpa [div_eq_mul_inv] using ha.neg.mul hd.inv) (by simpa [div_eq_mul_inv] using hb.neg.mul hd.inv) (by simpa [div_eq_mul_inv] using hc.neg.mul hd.inv) hrel
    exact EulerMascheroni.Arithmetic.gompertz_transcendental halg
  subst d
  simp only [Complex.ofReal_zero, zero_mul, add_zero] at h
  obtain ⟨rfl, rfl, rfl⟩ := e_values_linear_independent a b c ha hb hc h
  refine ⟨0, 0, 0, 0, ?_⟩
  simp
