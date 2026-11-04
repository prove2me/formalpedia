-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_b_smalljump_original_P2_monotone_mark_rate_extension
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T00:11:14.249744+00:00
-- url     : https://prove2.me/submissions/b497634b-ed57-493b-9779-a7276c72f442

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_intrinsic_marked_count_iUnion_of_monotone_bands

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Source P2 marked rates on an increasing sequence of original Borel
bands extend to the full union by physical-P monotone convergence. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (N : Ω → Measure (ℝ≥0 × ℝ))
    (hN : ∀ ω, N ω =
      (Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    (s t : ℝ≥0) (B : ℕ → Set ℝ) (hMon : Monotone B)
    (hMeas : ∀ n, Measurable
      (fun ω => N ω (Ioc s t ×ˢ B n)))
    (hRate : ∀ n,
      (∫⁻ ω, N ω (Ioc s t ×ˢ B n) ∂P) =
        (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (B n))) :
    (∫⁻ ω, N ω (Ioc s t ×ˢ (⋃ n, B n)) ∂P) =
      (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (⋃ n, B n)) := by
  have hCount (ω : Ω) :
      N ω (Ioc s t ×ˢ (⋃ n, B n)) =
        ⨆ n, N ω (Ioc s t ×ˢ B n) := by
    simpa only [hN ω] using
      (avram_p4_b_smalljump_original_intrinsic_marked_count_iUnion_of_monotone_bands
        X s t B hMon ω)
  have hMonoCount : Monotone
      (fun n : ℕ => fun ω : Ω => N ω (Ioc s t ×ˢ B n)) := by
    intro i j hij ω
    apply measure_mono
    rintro ⟨u, z⟩ ⟨hu, hz⟩
    exact ⟨hu, hMon hij hz⟩
  calc
    _ = (∫⁻ ω, ⨆ n, N ω (Ioc s t ×ˢ B n) ∂P) := by
      apply lintegral_congr_ae
      filter_upwards [] with ω
      exact hCount ω
    _ = ⨆ n, (∫⁻ ω, N ω (Ioc s t ×ˢ B n) ∂P) := by
      exact lintegral_iSup hMeas hMonoCount
    _ = ⨆ n, (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (B n)) := by
      simp only [hRate]
    _ = (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (⋃ n, B n)) := by
      rw [hMon.measure_iUnion, ENNReal.mul_iSup]
