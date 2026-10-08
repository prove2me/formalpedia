-- Prove2me | solution 1 for AvramDividend.Classical.admissible_cap_nat_horizon_bound_bounded_variation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T15:17:04.858162+00:00
-- url     : https://prove2.me/submissions/1844c063-567a-4c21-a6a5-a7c0a57477bb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_admissible_cap_truncated_dividendValue_le

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) :
    ∀ n : ℕ,
      (∫⁻ ω, ∫⁻ t in
          paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)),
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω) ∂P) ≤ ENNReal.ofReal (w x) := by
  have hsmooth :
      (¬ X.BoundedVariation →
        ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation →
        ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) := by
    constructor
    · intro h
      exact (h hBV).elim
    · intro _
      exact hw_smooth
  intro n
  have htrunc :=
    admissible_cap_truncated_dividendValue_le
      X hX q hq w C hC hw_cont hw0 hw_neg hsmooth hw_hjb
      x hx hxc D hD (n : ℝ) (by positivity)
  apply le_trans ?_ htrunc
  apply lintegral_mono
  intro ω
  apply lintegral_mono_set
  intro t ht
  have ht0 : 0 ≤ t := ht.1
  have hpay :
      t ∈ paymentTimes (ruinTime X x D ω) := by
    refine ⟨ht0, ?_⟩
    rcases ht.2 with hzero | hlt
    · exact Or.inl hzero
    · exact Or.inr (lt_of_lt_of_le hlt (min_le_left _ _))
  have htn : t ≤ (n : ℝ) := by
    rcases ht.2 with hzero | hlt
    · rw [hzero]
      positivity
    · have hlt' : ENNReal.ofReal t < (n : ℝ≥0∞) :=
        lt_of_lt_of_le hlt (min_le_right _ _)
      have hlt_nn : t < (n : ℝ≥0) :=
        (ENNReal.ofReal_lt_coe_iff ht0).mp hlt'
      exact le_of_lt hlt_nn
  exact ⟨hpay, htn⟩
