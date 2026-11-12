-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_phys118_original_dividend_rightLimit_ae_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T12:09:37.540881+00:00
-- url     : https://prove2.me/submissions/a4205ff6-3246-46ea-aacc-5aa2ad02d5ae

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys116_original_admissible_dividend_ae_continuity
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Topology

/-- The actual paper's infimum-based dividend right limit agrees
with the physical payment path at almost every positive time. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (μ : Measure ℝ≥0) [NullSingletonClass μ]
    (ω : Ω) :
    ∀ᵐ t ∂μ, rightLimit D t ω = D t ω := by
  have hzero :=
    avram_bvb_phys116_original_admissible_dividend_ae_continuity
      X x C D hD μ ω
  have hae : ∀ᵐ t ∂μ, ContinuousAt (fun s : ℝ≥0 => D s ω) t := by
    simpa only [Set.mem_setOf_eq, not_not] using
      (measure_eq_zero_iff_ae_notMem.mp hzero)
  filter_upwards [hae] with t ht
  have hmono : Monotone (fun s : ℝ≥0 => D s ω) := hD.1.1.2.1 ω
  calc
    rightLimit D t ω =
        sInf ((fun s : ℝ≥0 => D s ω) '' Ioi t) := by
          unfold rightLimit
          exact (sInf_image' (s := Ioi t)
            (f := fun s : ℝ≥0 => D s ω)).symm
    _ = Function.rightLim (fun s : ℝ≥0 => D s ω) t :=
      (hmono.rightLim_eq_sInf).symm
    _ = D t ω := ht.continuousWithinAt.rightLim_eq
