-- Prove2me | solution 1 for AvramDividend.Classical.chat04_unbounded_nonpositive_killed_renewal_of_near_zero
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T09:25:54.172799+00:00
-- url     : https://prove2.me/submissions/0b2a0f01-d321-4300-ad3a-ef6cd23a4561

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Theorems.Thm_AvramDividend_Classical_chat04_killed_survival_lintegral_zero_of_negative_initial_reserve
import Theorems.Thm_AvramDividend_Classical_chat04_killed_survival_lintegral_initial_nonnegative
import Theorems.Thm_AvramDividend_Classical_chat04_unbounded_zero_start_killed_renewal_of_ae_negative_near_zero

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnear : ∀ᵐ ω ∂P,
      ∀ ε : ℝ≥0, 0 < ε →
        ∃ s : ℝ≥0, s < ε ∧ X.X s ω < 0)
    (x : ℝ) (hx : x ≤ 0) (t : ℝ≥0) :
    (∫⁻ ω,
      ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator
        (fun ω => ENNReal.ofReal
          (Real.exp (-(q * (t : ℝ))) * W (x + X.X t ω))) ω ∂P) =
      ENNReal.ofReal (W x) := by
  rcases hx.lt_or_eq with hlt | rfl
  · exact AvramDividend.Classical.chat04_killed_survival_lintegral_zero_of_negative_initial_reserve
      X q W hW x hlt t
  · rcases (zero_le (a := t)).lt_or_eq with htpos | rfl
    · have h := AvramDividend.Classical.chat04_unbounded_zero_start_killed_renewal_of_ae_negative_near_zero
        X hnbv q hq W hW hnear t htpos
      simpa only [zero_add] using h
    · exact AvramDividend.Classical.chat04_killed_survival_lintegral_initial_nonnegative
        X q W 0 le_rfl
