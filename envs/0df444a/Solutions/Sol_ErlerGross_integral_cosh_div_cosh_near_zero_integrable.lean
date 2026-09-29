-- Prove2me | solution 1 for ErlerGross.integral_cosh_div_cosh_near_zero_integrable
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-26T18:05:51.101983+00:00
-- url     : https://prove2.me/submissions/af892c42-d7e7-4ee9-b52e-953420c78efc

import Mathlib

open MeasureTheory

theorem solution (a b : ℂ) (hab : |a.re| < b.re) :
    IntegrableOn (fun x : ℝ => Complex.cosh (a * x) / Complex.cosh (b * x))
      (Set.Ioo 0 1) := by
  have hb : 0 < b.re := lt_of_le_of_lt (abs_nonneg _) hab
  let f : ℝ → ℂ := fun x => Complex.cosh (a * x) / Complex.cosh (b * x)
  have hden : ∀ x ∈ Set.Icc (0 : ℝ) 1, Complex.cosh (b * (x : ℂ)) ≠ 0 := by
    intro x hx
    rcases hx with ⟨hx0, hx1⟩
    by_cases hxz : x = 0
    · simp [hxz]
    · have hxpos : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hxz)
      have hreal : (b * (x : ℂ)).re = b.re * x := by simp [Complex.mul_re]
      have hzpos : 0 < (b * (x : ℂ)).re := by rw [hreal]; exact mul_pos hb hxpos
      intro hc
      have hs : Complex.exp (b * (x : ℂ)) + Complex.exp (-(b * (x : ℂ))) = 0 := by
        rcases (div_eq_zero_iff.mp (by simpa only [Complex.cosh] using hc)) with hs | hs
        · exact hs
        · norm_num at hs
      have hu : Complex.exp (b * (x : ℂ)) = -Complex.exp (-(b * (x : ℂ))) :=
        eq_neg_of_add_eq_zero_left hs
      have heq : ‖Complex.exp (b * (x : ℂ))‖ = ‖Complex.exp (-(b * (x : ℂ)))‖ := by
        rw [hu, norm_neg]
      rw [Complex.norm_exp, Complex.norm_exp, Complex.neg_re] at heq
      have : (b * (x : ℂ)).re = -(b * (x : ℂ)).re := Real.exp_injective heq
      linarith
  have hcont : ContinuousOn f (Set.Icc (0 : ℝ) 1) := by
    change ContinuousOn (fun x : ℝ => Complex.cosh (a * (x : ℂ)) /
      Complex.cosh (b * (x : ℂ))) (Set.Icc (0 : ℝ) 1)
    exact (Complex.continuous_cosh.comp
      (continuous_const.mul Complex.continuous_ofReal)).continuousOn.div
      (Complex.continuous_cosh.comp
        (continuous_const.mul Complex.continuous_ofReal)).continuousOn
      (fun x hx => hden x hx)
  have hcompact : IntegrableOn f (Set.Icc (0 : ℝ) 1) :=
    hcont.integrableOn_compact isCompact_Icc
  exact hcompact.mono_set Set.Ioo_subset_Icc_self
