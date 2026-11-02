-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04c_actual_C1_global_weighted_Bernstein_payoff_tail
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T19:34:34.280227+00:00
-- url     : https://prove2.me/submissions/169c5e89-de98-44d9-8edb-006803ae097c

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_C1_logarithmic_quotient_continuous
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_tapered_compact_profile_quantitative
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_Bernstein_endpoint_weighted_polynomial_density
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open Set Filter
open AvramDividend.Classical

/-! Strong global C1 approximation: the far-tail majorant is the actual
payoff increment, not the potentially nonintegrable global jump first moment. -/
theorem solution (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w)
    (x a b ε : ℝ) (ha : 0 < a) (hab : a < b) (hb : b ≤ 1)
    (hε : 0 < ε) :
    ∃ Q : Polynomial ℝ, Polynomial.eval 1 Q = 0 ∧
      ∀ t : unitInterval.Elem, 0 < (t : ℝ) →
        |Polynomial.eval (t : ℝ) Q -
          (w x - w (x + Real.log (t : ℝ)))| ≤
          ε * (1 - (t : ℝ)) +
            (if (t : ℝ) < b
              then 2 * |w x - w (x + Real.log (t : ℝ))| else 0) := by
  let f : ℝ → ℝ :=
    Function.update
      (fun t : ℝ => (w (x + Real.log t) - w x) / (t - 1))
      1 (deriv w x)
  have hf : ContinuousOn f (Icc a 1) :=
    avram_wave5_04c_actual_C1_logarithmic_quotient_continuous
      w hw x a ha (le_trans (le_of_lt hab) hb)
  obtain ⟨G, hzero, hmatch, hbound⟩ :=
    avram_wave5_04c_tapered_compact_profile_quantitative f a b hab hb hf
  obtain ⟨Q, hQ, hQapprox⟩ :=
    avram_wave5_04c_Bernstein_endpoint_weighted_polynomial_density G ε hε
  let g : ℝ → ℝ := fun t => w x - w (x + Real.log t)
  have hcorrect (t : unitInterval.Elem) (ht : a ≤ (t : ℝ)) :
      (1 - (t : ℝ)) * f (t : ℝ) = g (t : ℝ) := by
    by_cases h1 : (t : ℝ) = 1
    · simp [g, h1]
    · have hfr : f (t : ℝ) =
          (w (x + Real.log (t : ℝ)) - w x) / ((t : ℝ) - 1) := by
        simp [f, h1]
      rw [hfr]
      have hne : (t : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr h1
      dsimp [g]
      field_simp
      ring
  have hGpayoff : ∀ t : unitInterval.Elem, 0 < (t : ℝ) →
      |(1 - (t : ℝ)) * G t| ≤ |g (t : ℝ)| := by
    intro t ht
    by_cases hta : (t : ℝ) ≤ a
    · rw [hzero t hta]
      simp
    · have hat : a ≤ (t : ℝ) := le_of_lt (lt_of_not_ge hta)
      have ht1 : (t : ℝ) ≤ 1 := t.property.2
      have hclamp : max a (min (t : ℝ) 1) = (t : ℝ) := by
        rw [min_eq_left ht1, max_eq_right hat]
      have hGb : |G t| ≤ |f (t : ℝ)| := by
        simpa only [hclamp] using hbound t
      calc
        |(1 - (t : ℝ)) * G t| =
          |1 - (t : ℝ)| * |G t| := abs_mul _ _
        _ ≤ |1 - (t : ℝ)| * |f (t : ℝ)| :=
          mul_le_mul_of_nonneg_left hGb (abs_nonneg _)
        _ = |(1 - (t : ℝ)) * f (t : ℝ)| := (abs_mul _ _).symm
        _ = |g (t : ℝ)| := by rw [hcorrect t hat]
  have hGmatch : ∀ t : unitInterval.Elem, b ≤ (t : ℝ) →
      (1 - (t : ℝ)) * G t = g (t : ℝ) := by
    intro t ht
    rw [hmatch t ht]
    exact hcorrect t (le_trans (le_of_lt hab) ht)
  refine ⟨Q, hQ, ?_⟩
  intro t ht
  by_cases htb : (t : ℝ) < b
  · have htri :
        |Polynomial.eval (t : ℝ) Q - g (t : ℝ)| ≤
        |Polynomial.eval (t : ℝ) Q - (1 - (t : ℝ)) * G t| +
        |(1 - (t : ℝ)) * G t - g (t : ℝ)| :=
      abs_sub_le _ _ _
    have htri2 :
        |(1 - (t : ℝ)) * G t - g (t : ℝ)| ≤
        |(1 - (t : ℝ)) * G t| + |g (t : ℝ)| := by
      simpa using (abs_sub_le ((1 - (t : ℝ)) * G t) (0 : ℝ) (g (t : ℝ)))
    have htotal := (htri.trans
      (add_le_add (hQapprox t) (htri2.trans (add_le_add (hGpayoff t ht) le_rfl))))
    change |Polynomial.eval (t : ℝ) Q - (w x - w (x + Real.log (t : ℝ)))| ≤
      ε * (1 - (t : ℝ)) +
        (if (t : ℝ) < b
          then 2 * |w x - w (x + Real.log (t : ℝ))| else 0)
    simpa [g, htb, two_mul] using htotal
  · have hb' : b ≤ (t : ℝ) := le_of_not_gt htb
    have hqt := hQapprox t
    rw [hGmatch t hb'] at hqt
    change |Polynomial.eval (t : ℝ) Q - (w x - w (x + Real.log (t : ℝ)))| ≤
      ε * (1 - (t : ℝ)) +
        (if (t : ℝ) < b
          then 2 * |w x - w (x + Real.log (t : ℝ))| else 0)
    simpa [g, htb] using hqt
