-- Prove2me | solution 1 for AvramDividend.Classical.barrier_comparison_of_finite_shape_and_secants
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-04T13:42:54.545722+00:00
-- url     : https://prove2.me/submissions/6021c977-beb8-414b-80bc-5cae5ada00d1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open AvramDividend.Classical
open scoped ENNReal

-- Mean-value bridge, including b=0 using continuity at the endpoint.
theorem secant_of_derivative_lower_bound (W : ℝ → ℝ) (c d : ℝ)
    (hcont : ContinuousOn W (Set.Icc 0 c))
    (hdiff : DifferentiableOn ℝ W (Set.Ioo 0 c))
    (hderiv : ∀ t ∈ Set.Ioo 0 c, d ≤ deriv W t) :
    ∀ b x : ℝ, 0 ≤ b → b ≤ x → x ≤ c →
      (x - b) * d ≤ W x - W b := by
  intro b x hb hbx hxc
  have hf : DifferentiableOn ℝ W (interior (Set.Icc 0 c)) := by
    simpa only [interior_Icc] using hdiff
  have hd : ∀ t ∈ interior (Set.Icc 0 c), d ≤ deriv W t := by
    simpa only [interior_Icc] using hderiv
  simpa only [mul_comm] using
    (convex_Icc (0 : ℝ) c).mul_sub_le_image_sub_of_le_deriv hcont hf hd
      b ⟨hb, hbx.trans hxc⟩ x ⟨hb.trans hbx, hxc⟩ hbx

-- Isolated conditional reduction, NOT the canonical milestone statement.
-- Source-reviewed only; no Lean execution or remote verification performed.
private theorem divE_le_ratio {y d : ℝ} {e : EReal}
    (hy : 0 ≤ y) (hd : 0 < d)
    (he : e = ⊤ ∨ e.toReal = 0 ∨ d ≤ e.toReal) :
    divE y e ≤ y / d := by
  unfold divE
  split_ifs with ht
  · exact div_nonneg hy hd.le
  · rcases he with he | he | he
    · exact (ht he).elim
    · simpa [he] using div_nonneg hy hd.le
    · exact div_le_div_of_nonneg_left hy hd he

private theorem barrier_comparison_of_secants
    (W : ℝ → ℝ) (c d : ℝ) (hd : 0 < d)
    (hc : scaleDeriv W c = (d : EReal))
    (hW : ∀ y : ℝ, 0 ≤ y → 0 ≤ W y)
    (hden : ∀ a : ℝ, 0 ≤ a →
      scaleDeriv W a = ⊤ ∨ (scaleDeriv W a).toReal = 0 ∨
        d ≤ (scaleDeriv W a).toReal)
    (hsec : ∀ b x : ℝ, 0 ≤ b → b ≤ x → x ≤ c →
      (x - b) * d ≤ W x - W b)
    (x a : ℝ) (hx : 0 ≤ x) (hxc : x ≤ c) (ha : 0 ≤ a) :
    barrierValue W a x ≤ barrierValue W c x := by
  have hright : barrierValue W c x = W x / d := by
    simp [barrierValue, not_lt.mpr hx, hxc, hc, divE]
  rw [hright]
  by_cases hxa : x ≤ a
  · simp only [barrierValue, if_neg (not_lt.mpr hx), if_pos hxa]
    exact divE_le_ratio (hW x hx) hd (hden a ha)
  · simp only [barrierValue, if_neg (not_lt.mpr hx), if_neg hxa]
    have hq := divE_le_ratio (hW a ha) hd (hden a ha)
    have hs := hsec a x ha (le_of_lt (lt_of_not_ge hxa)) hxc
    have hbound : x - a + W a / d ≤ W x / d := by
      apply (le_div_iff₀ hd).2
      have hcancel := div_mul_cancel₀ (W a) (ne_of_gt hd)
      nlinarith
    linarith

-- The first alternative covers c*=0 and W(0)=0 even for infinite or zero
-- one-sided derivative. The second covers a finite positive denominator at c*.
theorem solution (W : ℝ → ℝ) (hfinite : cstar W < ⊤)
    (hW : ∀ y : ℝ, 0 ≤ y → 0 ≤ W y)
    (hshape : ((cstar W).toReal = 0 ∧ W 0 = 0) ∨
      ∃ d : ℝ, 0 < d ∧ scaleDeriv W (cstar W).toReal = (d : EReal) ∧
        (∀ a : ℝ, 0 ≤ a →
          scaleDeriv W a = ⊤ ∨ (scaleDeriv W a).toReal = 0 ∨
            d ≤ (scaleDeriv W a).toReal) ∧
        (∀ b x : ℝ, 0 ≤ b → b ≤ x → x ≤ (cstar W).toReal →
          (x - b) * d ≤ W x - W b)) :
    cstar W < ⊤ ∧
      ∀ x a : ℝ, 0 ≤ x → x ≤ (cstar W).toReal → 0 ≤ a →
        barrierValue W a x ≤ vcstar W x := by
  refine ⟨hfinite, ?_⟩
  intro x a hx hxc ha
  rcases hshape with ⟨hc, hzero⟩ | ⟨d, hd, hc, hden, hsec⟩
  · have hxzero : x = 0 := by linarith
    subst x
    simp [vcstar, hc, barrierValue, ha, hzero, divE]
  · exact barrier_comparison_of_secants W (cstar W).toReal d hd hc hW
      hden hsec x a hx hxc ha
