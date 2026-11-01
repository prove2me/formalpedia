-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04b_atomless_pre_source_pre_payment_ae_of_countable_jumps
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T10:50:10.406197+00:00
-- url     : https://prove2.me/submissions/d2d552f7-f074-43ab-bdd0-184e7e8d809b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_atomless_right_limit_eq_pre_payment_ae

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

noncomputable section

set_option maxHeartbeats 1000000 in
/-- A source with countably many positive left-jump times and an adapted dividend
strategy have their chronological pre-source/pre-payment reserve identified
almost everywhere for any atomless dividend-control component. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω)
    (hcount : Set.Countable {t : ℝ≥0 |
      0 < t ∧ X.X t ω ≠ Function.leftLim
        (fun r : ℝ≥0 => X.X r ω) t})
    (ν : Measure ℝ) [NullSingletonClass ν] :
    ∀ᵐ s ∂ν, 0 < s →
      riskProcess X x D s.toNNReal ω =
        x + Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal -
          rightLimit D s.toNNReal ω := by
  have hcountReal :
      Set.Countable {s : ℝ | 0 < s ∧
        X.X s.toNNReal ω ≠ Function.leftLim
          (fun r : ℝ≥0 => X.X r ω) s.toNNReal} := by
    have hImage :
        Set.Countable
          ((fun t : ℝ≥0 => (t : ℝ)) ''
            {t : ℝ≥0 | 0 < t ∧
              X.X t ω ≠ Function.leftLim
                (fun r : ℝ≥0 => X.X r ω) t}) :=
      hcount.image (fun t : ℝ≥0 => (t : ℝ))
    apply hImage.mono
    intro s hs
    have hcoe : (s.toNNReal : ℝ) = s :=
      Real.coe_toNNReal s (le_of_lt hs.1)
    have hreal : (0 : ℝ) < (s.toNNReal : ℝ) := by
      simpa only [hcoe] using hs.1
    have hnn : (0 : ℝ≥0) < s.toNNReal := by
      exact_mod_cast hreal
    refine ⟨s.toNNReal, ⟨hnn, hs.2⟩, hcoe⟩
  have hXae :
      ∀ᵐ s ∂ν, 0 < s →
        X.X s.toNNReal ω =
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal := by
    apply ae_iff.mpr
    have hzero :
        ν {s : ℝ | 0 < s ∧
          X.X s.toNNReal ω ≠ Function.leftLim
            (fun r : ℝ≥0 => X.X r ω) s.toNNReal} = 0 :=
      hcountReal.measure_zero ν
    simpa only [_root_.not_imp] using hzero
  have hDae :
      ∀ᵐ s ∂ν, 0 ≤ s →
        rightLimit D s.toNNReal ω = D s.toNNReal ω :=
    avram_wave4_04b_atomless_right_limit_eq_pre_payment_ae D hD ω ν
  filter_upwards [hXae, hDae] with s hXeq hDeq hs
  have hx := hXeq hs
  have hd := hDeq (le_of_lt hs)
  change x + X.X s.toNNReal ω - D s.toNNReal ω =
    x + Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal -
      rightLimit D s.toNNReal ω
  rw [hx, hd]
