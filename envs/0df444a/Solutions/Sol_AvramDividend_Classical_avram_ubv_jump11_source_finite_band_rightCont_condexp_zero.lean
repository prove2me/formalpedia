-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_jump11_source_finite_band_rightCont_condexp_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T10:04:05.765207+00:00
-- url     : https://prove2.me/submissions/0e8c5d10-fd81-4b22-9a85-4a7a7d221aa7

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_intrinsic_borel_marked_unconditional_levy_rate
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_rectangle_of_unconditional_rate
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_P2_raw_implies_rightCont_finite_band_centering
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (r : ℕ → ℝ≥0)
    (hsr : ∀ n, s < r n) (hrt : ∀ n, r n ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B)
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
    (hFinite : X.ν B ≠ ⊤) (hJmeas : Measurable (J s t)) :
    P[(fun ω => (J s t ω).toReal -
      (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal) |
      𝓕.rightCont s] =ᵐ[P] 0 := by
  have hMass : ∀ C : Set Ω,
      MeasurableSet[𝓕.rightCont s] C → P C ≠ ⊤ := by
    intro C _
    exact ne_of_lt (measure_lt_top P C)
  have hRate (n : ℕ) :
      (∫⁻ ω, J s (r n) ω ∂P) =
        ((r n - s : ℝ≥0) : ℝ≥0∞) * X.ν B := by
    simpa only [hJsource] using
      (avram_wave7_01_original_intrinsic_borel_marked_unconditional_levy_rate
        X s (r n) (hsr n).le B hB)
  have hRaw (u v : ℝ≥0) (C : Set Ω)
      (huv : u ≤ v) (hC : MeasurableSet[𝓕 u] C) :
      (∫⁻ ω in C, J u v ω ∂P) =
        P C * ((v - u : ℝ≥0) : ℝ≥0∞) * X.ν B := by
    simpa only [hJsource] using
      (avram_p2_e_compensator_original_rectangle_of_unconditional_rate
        X u v huv C hC B hB
        (avram_wave7_01_original_intrinsic_borel_marked_unconditional_levy_rate
          X u v huv B hB))
  have hFullRate :
      (∫⁻ ω, J s t ω ∂P) =
        ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B := by
    simpa only [hJsource] using
      (avram_wave7_01_original_intrinsic_borel_marked_unconditional_levy_rate
        X s t (le_trans (le_of_lt (hsr 0)) (hrt 0)) B hB)
  exact avram_p4_b_smalljump_original_P2_raw_implies_rightCont_finite_band_centering
    X s t r hsr hrt B hB J hJsource hShort hLong
    hFinite hMass hRate hRaw hJmeas hFullRate
