-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB40_barrier_lower_hit_clock_equals_horizon_on_tube
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T16:16:40.55451+00:00
-- url     : https://prove2.me/submissions/a9b40110-6b26-4676-819c-7d85c2143dc3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB38_barrier_reserve_above_cutoff_on_tube
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
noncomputable section
/-- On a narrow source tube the original lower-hit stopping clock equals T. -/
theorem solution
  {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 mΩ}
  (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (ω : Ω)
  (hTube : ∀ s : ℝ≥0, s ≤ T →
    |X.X s ω| ≤ (1 / 400 : ℝ)) :
  sInf ((Icc (0 : ℝ≥0) T ∩
    (fun t : ℝ≥0 => -(riskProcess X (1 / 8 : ℝ)
      (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) t ω)) ⁻¹'
      Ici (-(5 / 44 : ℝ))) ∪ {T}) = T := by
  classical
  have hEmpty :
      Icc (0 : ℝ≥0) T ∩
        (fun t : ℝ≥0 => -(riskProcess X (1 / 8 : ℝ)
          (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) t ω)) ⁻¹'
        Ici (-(5 / 44 : ℝ)) = ∅ := by
    ext t
    constructor
    · intro ht
      have hB :=
        avram_gbB38_barrier_reserve_above_cutoff_on_tube X t ω
          (fun s hs => hTube s (hs.trans ht.1.2))
      have hBad : -(5 / 44 : ℝ) ≤
          -(riskProcess X (1 / 8 : ℝ)
            (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) t ω) :=
        ht.2
      linarith
    · simp
  simpa only [hEmpty, Set.empty_union] using (csInf_singleton T)
