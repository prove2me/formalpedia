-- Prove2me | solution 1 for AvramDividend.Classical.cstar_zero_barrier_compare_of_positive_boundary
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T15:32:49.684266+00:00
-- url     : https://prove2.me/submissions/41426acc-4e56-47e3-aa6d-7c744df6cc37

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_cstar_optimal_barrier_of_shape

open AvramDividend.Classical
open scoped ENNReal

theorem solution (W : ℝ → ℝ)
    (hnonneg : ∀ y : ℝ, 0 ≤ y → 0 ≤ W y)
    (hno : ¬(cstarSet W).Nonempty)
    (hderivmin : ∀ x : ℝ, 0 < x →
      derivZeroPlus W ≤ ((deriv W x : ℝ) : EReal))
    (d : ℝ) (hd : 0 < d)
    (hboundary : derivZeroPlus W = (d : EReal)) :
    cstar W < ⊤ ∧
      ∀ x a : ℝ, 0 ≤ x → x ≤ (cstar W).toReal → 0 ≤ a →
        barrierValue W a x ≤ vcstar W x := by
  have hc : cstar W = (0 : ℝ≥0∞) := by
    unfold cstar
    rw [if_neg hno, if_pos hderivmin]
  have hf : cstar W < ⊤ := by
    simp [hc]
  have hscale : scaleDeriv W (cstar W).toReal = (d : EReal) := by
    simp [hc, scaleDeriv, hboundary]
  have hden : ∀ a : ℝ, 0 ≤ a →
      scaleDeriv W a = ⊤ ∨
        (scaleDeriv W a).toReal = 0 ∨
        d ≤ (scaleDeriv W a).toReal := by
    intro a ha
    right
    right
    by_cases ha0 : a = 0
    · subst a
      simpa [scaleDeriv, hboundary] using (le_refl d)
    · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      have hle : (d : EReal) ≤ ((deriv W a : ℝ) : EReal) := by
        simpa only [hboundary] using hderivmin a hapos
      have hr : d ≤ deriv W a := by
        exact_mod_cast hle
      simpa [scaleDeriv, ha0] using hr
  apply cstar_optimal_barrier_of_shape W hf hnonneg
  right
  refine ⟨d, hd, hscale, hden, ?_⟩
  intro b x hb hbx hxc
  have hx0 : x ≤ 0 := by
    simpa only [hc, ENNReal.toReal_zero] using hxc
  have heqx : x = 0 := by
    linarith
  have heqb : b = 0 := by
    linarith
  subst x
  subst b
  simp
