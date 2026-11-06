-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_s3_interval_g_original_rightcont_same_window_mark_simple_L2_martingale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T14:48:39.073766+00:00
-- url     : https://prove2.me/submissions/d0031a77-7acb-4142-baf4-deaf152f3864

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04_source_rightCont_levy_lift
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_e_original_same_window_mark_simple_L2_martingale
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (cut : ℕ)
    (s t : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T)
    (ε : ℝ) (hε : 0 < ε) (B : ι → Set ℝ)
    (hB : ∀ i, MeasurableSet (B i))
    (hBand : ∀ i, B i ⊆ Ioo (-1 : ℝ) (-ε))
    (hCut : ∀ i, B i ⊆ Iic (-(1 / ((cut : ℝ) + 1))))
    (H : ι → Ω → ℝ)
    (hH : ∀ i, StronglyMeasurable[𝓕.rightCont s] (H i))
    (hHL2 : ∀ i, MemLp (H i) 2 P)
    (L : ℝ) (hBound : ∀ i ω, |H i ω| ≤ L)
    (F : Finset ι) :
    let Z : ι → Ω → ℝ := fun i ω =>
      H i ω * (((((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B i)).toReal) -
          (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (B i)).toReal)
    MemLp (∑ i ∈ F, Z i) 2 P ∧
    P[(∑ i ∈ F, Z i) | 𝓕.rightCont s] =ᵐ[P] (0 : Ω → ℝ) := by
  obtain ⟨Y, hYX, hc, hσ, hνEq⟩ :=
    avram_wave5_04_source_rightCont_levy_lift X
  simpa only [hYX, hνEq] using
    (avram_p4_s3_interval_e_original_same_window_mark_simple_L2_martingale
      Y T cut s t hst htT ε hε B hB hBand hCut
      H hH hHL2 L hBound F)
