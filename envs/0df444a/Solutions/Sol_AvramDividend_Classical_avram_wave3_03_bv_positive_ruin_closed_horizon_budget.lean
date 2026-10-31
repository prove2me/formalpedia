-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_03_bv_positive_ruin_closed_horizon_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T12:21:40.675729+00:00
-- url     : https://prove2.me/submissions/71f68b72-751c-4a70-98c3-37de88b7b762

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_positive_ruin_strict_stopped_drift_budget

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The complete original closed-horizon dividend reward, including the
    terminal Stieltjes atom, embeds in a strictly later stopped reward. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q) (T H : ℝ≥0) (hTH : T < H) :
    ∀ᵐ ω ∂P, 0 < ruinTime X x D ω →
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)) ≤
        ENNReal.ofReal (x + (H : ℝ) * X.drift) := by
  have hH : (0 : ℝ≥0) < H :=
    lt_of_le_of_lt (show (0 : ℝ≥0) ≤ T from zero_le) hTH
  have hHtop : (T : ℝ≥0∞) < (H : ℝ≥0∞) := by exact_mod_cast hTH
  filter_upwards
      [avram_wave3_03_bv_positive_ruin_strict_stopped_drift_budget
        X hX hBV x D hD q hq H hH] with ω hbudget
  intro hruin
  have hsub : paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ) ⊆
      paymentTimes (min (ruinTime X x D ω) (H : ℝ≥0∞)) := by
    intro t ht
    have htzero : 0 ≤ t := (show t ∈ paymentTimes (ruinTime X x D ω) from ht.1).1
    have hltH : ENNReal.ofReal t < (H : ℝ≥0∞) := by
      have htt : ENNReal.ofReal t ≤ (T : ℝ≥0∞) := by
        calc
          ENNReal.ofReal t ≤ ENNReal.ofReal (T : ℝ) :=
            ENNReal.ofReal_le_ofReal ht.2
          _ = (T : ℝ≥0∞) := by simp
      exact lt_of_le_of_lt htt hHtop
    simp only [paymentTimes, Set.mem_setOf_eq] at ht ⊢
    rcases ht.1.2 with ht0 | htRu
    · exact ⟨htzero, Or.inl ht0⟩
    · exact ⟨htzero, Or.inr (lt_min htRu hltH)⟩
  exact (lintegral_mono_set hsub).trans (hbudget hruin)
