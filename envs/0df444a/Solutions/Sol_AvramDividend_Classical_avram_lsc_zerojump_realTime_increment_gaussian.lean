-- Prove2me | solution 1 for AvramDividend.Classical.avram_lsc_zerojump_realTime_increment_gaussian
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T15:30:41.165455+00:00
-- url     : https://prove2.me/submissions/1b4892da-fa49-4870-ad75-ad38d7759c8c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gbB264_original_zerojump_normalised_increment_exact_gaussian_law

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Real-time transport of the intrinsic Gaussian increment law. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0) (hσ : 0 < X.σ)
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) :
    Measure.map (fun ω =>
      ((X.X (Real.toNNReal t) ω - X.X (Real.toNNReal s) ω) -
        (t - s) * X.c) / X.σ) P =
      gaussianReal 0 (Real.toNNReal (t - s)) := by
  have ht : 0 ≤ t := le_trans hs hst
  have hstNN : Real.toNNReal s ≤ Real.toNNReal t :=
    Real.toNNReal_le_toNNReal hst
  have hd : ((Real.toNNReal t - Real.toNNReal s : ℝ≥0) : ℝ) = t - s := by
    rw [NNReal.coe_sub hstNN]
    simp [Real.coe_toNNReal _ ht, Real.coe_toNNReal _ hs]
  have hv : (Real.toNNReal t - Real.toNNReal s : ℝ≥0) =
      Real.toNNReal (t - s) := by
    apply NNReal.coe_injective
    rw [hd, Real.coe_toNNReal _ (sub_nonneg.mpr hst)]
  have hbase :=
    AvramDividend.Classical.avram_gbB264_original_zerojump_normalised_increment_exact_gaussian_law
      X hν hσ (Real.toNNReal s) (Real.toNNReal t) hstNN
  rw [hd, hv] at hbase
  exact hbase
