-- Prove2me | solution 1 for AvramDividend.Classical.avram_b52_original_gaussian_and_marked_jump_predictable_cell_centered
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T10:06:57.987441+00:00
-- url     : https://prove2.me/submissions/bdf7ba94-a3cb-40e7-922d-4d9e70e630bc

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_b31_original_finite_activity_intrinsic_gaussian_martingale_exists
import Theorems.Thm_AvramDividend_Classical_avram_jb20_original_gaussian_past_weight_increment_mean_zero
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_unbounded_predictable_cell_L1_integral_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Source-original Gaussian plus negative Borel-mark predictable compensated jump cell is centred. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∃ R : ℝ≥0 → Ω → ℝ,
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        Tendsto (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
          atTop (𝓝 (R t ω))) ∧
      ∀ (T : ℝ≥0) (cut : ℕ)
        (s t : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T)
        (ε : ℝ) (hε : 0 < ε) (B : Set ℝ)
        (hB : MeasurableSet B)
        (hBand : B ⊆ Ioo (-1 : ℝ) (-ε))
        (hCut : B ⊆ Iic (-(1 / ((cut : ℝ) + 1))))
        (HG HJ : Ω → ℝ)
        (hHG : Measurable[𝓕.rightCont s] HG)
        (hHJI : StronglyMeasurable[𝓕 s] HJ)
        (hHJ2 : MemLp HJ 2 P)
        (hGI : Integrable (fun ω =>
          HG ω * (R t ω - R s ω)) P),
        let N : Ω → ℝ≥0∞ := fun ω =>
          ((Measure.count.restrict {u : ℝ≥0 |
            0 < u ∧ X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u, X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
            (Ioc s t ×ˢ B)
        let r : ℝ := (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal
        Integrable (fun ω =>
          HG ω * (R t ω - R s ω) + HJ ω * ((N ω).toReal - r)) P ∧
        (∫ ω, HG ω * (R t ω - R s ω) +
          HJ ω * ((N ω).toReal - r) ∂P) = 0 := by 
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  obtain ⟨R, hRsource, hRmeas, hRI, hRM⟩ :=
    avram_b31_original_finite_activity_intrinsic_gaussian_martingale_exists
      X hX hFinite
  refine ⟨R, ?_, ?_⟩
  · filter_upwards [hRsource] with ω hw t
    exact hw.1 t
  intro T cut s t hst htT ε hε B hB hBand hCut
    HG HJ hHG hHJI hHJ2 hGI
  dsimp only
  have hGzero :=
    avram_jb20_original_gaussian_past_weight_increment_mean_zero
      R hRI hRM s t hst HG hHG hGI
  have hJ :=
    avram_p4_f3_original_unbounded_predictable_cell_L1_integral_zero
      X T cut s t hst htT ε hε B hB hBand hCut HJ hHJI hHJ2
  dsimp only at hJ
  refine ⟨hGI.add hJ.1, ?_⟩
  rw [integral_add hGI hJ.1, hGzero, hJ.2]
  simp
