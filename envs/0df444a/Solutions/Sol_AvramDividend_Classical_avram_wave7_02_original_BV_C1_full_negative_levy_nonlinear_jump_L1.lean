-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_02_original_BV_C1_full_negative_levy_nonlinear_jump_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T16:38:31.830782+00:00
-- url     : https://prove2.me/submissions/2deed9d7-7f8d-44fe-b09e-7638043fb23d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_C1_actual_small_levy_mark_nonlinear_discounted_L1
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_C1_negative_large_mark_discounted_levy_L1_on_true_tail
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Actual original bounded-variation C1 stopped source has a full
negative-mark L1 kernel: small first-variation plus finite large-mark mass. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ)
    (q : ℝ) (hq : 0 ≤ q)
    (a b L R : ℝ) (ha : 0 < a) (ha2 : a ≤ 2) (hab : a ≤ b)
    (hL : 0 ≤ L) (hR : 0 ≤ R)
    (hLip : ∀ u ∈ Icc (a / 2) b, ∀ v ∈ Icc (a / 2) b,
      |w u - w v| ≤ L * |u - v|)
    (hWbound : ∀ v : ℝ, v ≤ b → |w v| ≤ R)
    (ω : Ω) (t : ℝ≥0)
    (hBand : Function.leftLim (fun s : ℝ≥0 =>
      x + X.X s ω - rightLimit D s ω) t ∈ Icc a b)
    (hMass : X.ν (Iic (-a / 2)) < ⊤)
    (F : ℝ → ℝ)
    (hF : F = fun z =>
      Real.exp (-(q * (t : ℝ))) *
        (w (Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s ω - rightLimit D s ω) t + z) -
         w (Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s ω - rightLimit D s ω) t)))
    (hSmallMeas : AEStronglyMeasurable F
      (X.ν.restrict (Ioo (-a / 2) 0)))
    (hLargeMeas : AEStronglyMeasurable F
      (X.ν.restrict (Iic (-a / 2)))) :
    IntegrableOn F (Iio 0) X.ν := by
  subst F
  have hSmall :=
    avram_wave7_02_original_BV_C1_actual_small_levy_mark_nonlinear_discounted_L1
      X hBV x D w q hq a b L ha ha2 hab hL hLip ω t hBand hSmallMeas
  have hLarge :=
    avram_wave7_02_original_BV_C1_negative_large_mark_discounted_levy_L1_on_true_tail
      X x D w q hq a b R ha hab hR hWbound ω t hBand hMass hLargeMeas
  have hCover : Iic (-a / 2) ∪ Ioo (-a / 2) (0 : ℝ) = Iio 0 := by
    ext z
    simp only [mem_union, mem_Iic, mem_Ioo, mem_Iio]
    constructor
    · intro hz
      rcases hz with hz | ⟨_, hz⟩
      · have hcut : -a / 2 < (0 : ℝ) := by linarith
        exact lt_of_le_of_lt hz hcut
      · exact hz
    · intro hz
      by_cases hcut : z ≤ -a / 2
      · exact Or.inl hcut
      · exact Or.inr ⟨lt_of_not_ge hcut, hz⟩
  rw [← hCover]
  exact hLarge.union hSmall
