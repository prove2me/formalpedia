-- Prove2me | solution 2 for AvramDividend.Classical.barrier_cstar_global_value_upper_bound_of_generator
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T09:35:13.526728+00:00
-- url     : https://prove2.me/submissions/1b2b7cae-c548-449f-96bb-8871e973e70f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_vcstar_unrestricted_verification_regularity
import Theorems.Thm_AvramDividend_Classical_vcstar_hjb_all_positive_of_generator
import Theorems.Thm_AvramDividend_Classical_local_verification

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Global comparison from the full positive HJB and local verification at top cap. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨ ContDiffOn ℝ 2 (vcstar W) (Ioi 0))
    (hgen : ∀ y : ℝ, (cstar W).toReal < y →
      X.GeneratorIntegrable (vcstar W) y ∧
        X.generator (vcstar W) y - q * vcstar W y ≤ 0) :
    ∀ x : ℝ, 0 ≤ x →
      valueFunction X q x ≤ ENNReal.ofReal (vcstar W x) := by
  obtain ⟨hcont, hw0, hwneg, hsmooth⟩ :=
    vcstar_unrestricted_verification_regularity X hX q hq W hW hc h_smooth
  have hsubset :
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < (⊤ : ℝ≥0∞)} ⊆ Ioi (0 : ℝ) := by
    intro y hy
    exact hy.1
  have hsmooth_top :
      (¬ X.BoundedVariation →
        ContDiffOn ℝ 2 (vcstar W)
          {y : ℝ | 0 < y ∧ ENNReal.ofReal y < (⊤ : ℝ≥0∞)}) ∧
      (X.BoundedVariation →
        ContDiffOn ℝ 1 (vcstar W)
          {y : ℝ | 0 < y ∧ ENNReal.ofReal y < (⊤ : ℝ≥0∞)}) :=
    ⟨fun hb => (hsmooth.1 hb).mono hsubset,
     fun hb => (hsmooth.2 hb).mono hsubset⟩
  have hhjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < (⊤ : ℝ≥0∞) →
      X.GeneratorIntegrable (vcstar W) y ∧
        max (X.generator (vcstar W) y - q * vcstar W y)
            (1 - deriv (vcstar W) y) = 0 := by
    intro y hy _
    exact vcstar_hjb_all_positive_of_generator
      X hX q hq W hW hc h_smooth hgen y hy
  have htop : (0 : ℝ≥0∞) < ⊤ := ENNReal.zero_lt_top
  obtain ⟨_, hglobal⟩ := local_verification X hX q hq
    (vcstar W) ⊤ htop hcont hw0 hwneg hsmooth_top hhjb
  exact hglobal rfl
