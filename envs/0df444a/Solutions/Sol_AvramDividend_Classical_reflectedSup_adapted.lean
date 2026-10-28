-- Prove2me | solution 1 for AvramDividend.Classical.reflectedSup_adapted
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T20:27:06.131274+00:00
-- url     : https://prove2.me/submissions/3b8074d1-6ed2-4377-9427-de0d1ca43dca

import Mathlib.Probability.Process.Adapted
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_adapted
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_self_eq_runningSup
import Definitions.Def_AvramDividend_Classical_Reflection

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    Adapted 𝓕 (fun t : ℝ≥0 => fun ω : Ω => reflectedSup X t ω) := by
  have heq : barrierStrategy X (0 : ℝ) 0 = runningSup X := by
    funext t ω
    exact barrierStrategy_self_eq_runningSup X 0 ω t
  have hS : Adapted 𝓕 (runningSup X) := by
    rw [← heq]
    exact barrierStrategy_adapted X 0
  change Adapted 𝓕 (fun t : ℝ≥0 => fun ω : Ω =>
    runningSup X t ω - X.X t ω)
  exact hS.sub X.adapted
