-- Prove2me | solution 1 for AvramDividend.Classical.avram_e0_initial_mark_source_positive_ruin_time
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T22:09:10.273208+00:00
-- url     : https://prove2.me/submissions/de8abe5f-374e-4c6e-8f51-30ffc6886698

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_e0_initial_mark_allpath_positive_ruin_time
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-! The source Levy structure itself supplies every pathwise zero-clock premise. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (K : Ω → ℝ)
    (hKnonneg : ∀ ω, 0 ≤ K ω)
    (hKstrict : ∀ ω, K ω < x) :
    ∀ ω, (0 : ℝ≥0∞) <
      ruinTime X x (fun t η => if t = 0 then 0 else K η) ω := by
  apply avram_e0_initial_mark_allpath_positive_ruin_time
    X x K hKnonneg hKstrict
  · exact X.X_zero
  · intro ω
    have hset : (Set.Ici (0 : ℝ≥0)) = Set.univ := by ext t; simp
    have hc : ContinuousWithinAt (fun t : ℝ≥0 => X.X t ω) Set.univ 0 := by
      simpa only [hset] using (X.rightCont ω 0)
    exact (continuousWithinAt_univ (fun t : ℝ≥0 => X.X t ω) 0).mp hc
