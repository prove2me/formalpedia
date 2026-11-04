-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_b_smalljump_original_rightCont_event_rate_of_nearby_future
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T22:09:00.585187+00:00
-- url     : https://prove2.me/submissions/71578463-532a-4665-8067-0e28b7925b40

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_short_strip_future_rate_sandwich

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped ENNReal NNReal

/-- The actual original intrinsic Lévy count inherits an eventwise future
rate at a right-continuous starting time from source rates immediately after
that time. Finite physical mark intensity controls the omitted short strip. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (r : ℕ → ℝ≥0)
    (hsr : ∀ n, s ≤ r n) (hrt : ∀ n, r n ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B) (A : Set Ω)
    (J : ℝ≥0 → ℝ≥0 → Ω → ℝ≥0∞)
    (hJsource : ∀ a b ω, J a b ω =
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
       (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
       (Ioc a b ×ˢ B))
    (hShort : Tendsto (fun n => r n - s) atTop (𝓝 0))
    (hLong : Tendsto (fun n => t - r n) atTop (𝓝 (t - s)))
    (hFinite : X.ν B ≠ ⊤) (hMass : P A ≠ ⊤)
    (hRate : ∀ n, (∫⁻ ω, J s (r n) ω ∂P) =
      ((r n - s : ℝ≥0) : ℝ≥0∞) * X.ν B)
    (hFuture : ∀ n, (∫⁻ ω in A, J (r n) t ω ∂P) =
      P A * ((t - r n : ℝ≥0) : ℝ≥0∞) * X.ν B) :
    (∫⁻ ω in A, J s t ω ∂P) =
      P A * ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B := by
  have hShortC : Tendsto
      (fun n => ((r n - s : ℝ≥0) : ℝ≥0∞)) atTop (𝓝 0) :=
    (ENNReal.continuous_coe.tendsto 0).comp hShort
  have hLongC : Tendsto
      (fun n => ((t - r n : ℝ≥0) : ℝ≥0∞))
      atTop (𝓝 ((t - s : ℝ≥0) : ℝ≥0∞)) :=
    (ENNReal.continuous_coe.tendsto (t - s)).comp hLong
  have hSmallRate : Tendsto
      (fun n => ((r n - s : ℝ≥0) : ℝ≥0∞) * X.ν B)
      atTop (𝓝 0) := by
    simpa only [zero_mul] using
      (ENNReal.Tendsto.mul_const hShortC (Or.inr hFinite))
  have hLongRate : Tendsto
      (fun n => P A * ((t - r n : ℝ≥0) : ℝ≥0∞) * X.ν B)
      atTop (𝓝 (P A * ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B)) := by
    have h₁ := ENNReal.Tendsto.mul_const hLongC (Or.inr hFinite)
    have h₂ := ENNReal.Tendsto.mul_const h₁ (Or.inr hMass)
    simpa only [mul_comm, mul_left_comm, mul_assoc] using h₂
  have hUpper : Tendsto
      (fun n => ((r n - s : ℝ≥0) : ℝ≥0∞) * X.ν B +
        P A * ((t - r n : ℝ≥0) : ℝ≥0∞) * X.ν B)
      atTop (𝓝 (P A * ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B)) := by
    simpa only [zero_add] using hSmallRate.add hLongRate
  have hBounds (n : ℕ) :=
    avram_p4_b_smalljump_original_short_strip_future_rate_sandwich
      X s (r n) t (hsr n) (hrt n) B hB A J hJsource (hRate n) (hFuture n)
  have hMiddle : Tendsto
      (fun _ : ℕ => (∫⁻ ω in A, J s t ω ∂P)) atTop
      (𝓝 (P A * ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B)) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le
      hLongRate hUpper (fun n => (hBounds n).1) (fun n => (hBounds n).2)
  exact tendsto_nhds_unique tendsto_const_nhds hMiddle
