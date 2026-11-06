-- Prove2me | solution 1 for AvramDividend.Classical.avram_sweep16_original_double_min_clock_rightcont_stopping
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T18:23:29.821536+00:00
-- url     : https://prove2.me/submissions/8d76b5e9-1088-4688-84dc-358884212832

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_ruinTime_stopping_rightCont_filtration
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
/-! The exact original ruin clock, deterministic cap and physical
    localiser are all right-continuous-filtration stopping times. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (S : ℕ → Ω → ℝ≥0∞)
    (hSstop : ∀ k, IsStoppingTime 𝓕.rightCont (S k)) :
    ∀ k, IsStoppingTime 𝓕.rightCont
      (fun ω => min (min (ruinTime X x D ω) (n : ℝ≥0∞)) (S k ω)) := by
  intro k
  have hRuin := ruinTime_stopping_rightCont_filtration X x D hD.1.1
  have hNat : IsStoppingTime 𝓕.rightCont
      (fun _ : Ω => (n : WithTop ℝ≥0)) :=
    isStoppingTime_const 𝓕.rightCont (n : ℝ≥0)
  exact (hRuin.min hNat).min (hSstop k)
