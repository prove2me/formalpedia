-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_b_smalljump_original_raw_compensator_to_rightCont_event_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T22:17:18.952507+00:00
-- url     : https://prove2.me/submissions/37dd2196-0747-455c-a291-322f2d8c14c0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_rightCont_event_raw_after
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_rightCont_event_rate_of_nearby_future

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The original raw marked-jump rectangle compensator propagates to the
actual right-continuous source filtration through future-time limits.
No alternative jump process or stochastic measure is introduced. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (r : ℕ → ℝ≥0)
    (hsr : ∀ n, s < r n) (hrt : ∀ n, r n ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B) (A : Set Ω)
    (hA : MeasurableSet[𝓕.rightCont s] A)
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
    (hRaw : ∀ (u v : ℝ≥0) (C : Set Ω), u ≤ v →
      MeasurableSet[𝓕 u] C →
      (∫⁻ ω in C, J u v ω ∂P) =
        P C * ((v - u : ℝ≥0) : ℝ≥0∞) * X.ν B) :
    (∫⁻ ω in A, J s t ω ∂P) =
      P A * ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B := by
  have hFuture (n : ℕ) :
      (∫⁻ ω in A, J (r n) t ω ∂P) =
        P A * ((t - r n : ℝ≥0) : ℝ≥0∞) * X.ν B :=
    hRaw (r n) t A (hrt n)
      (avram_p4_b_smalljump_original_rightCont_event_raw_after X (hsr n) hA)
  exact avram_p4_b_smalljump_original_rightCont_event_rate_of_nearby_future
    X s t r (fun n => (hsr n).le) hrt B hB A J hJsource
    hShort hLong hFinite hMass hRate hFuture
