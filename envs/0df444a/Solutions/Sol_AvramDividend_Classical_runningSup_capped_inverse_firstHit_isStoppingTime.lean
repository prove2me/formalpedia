-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_capped_inverse_firstHit_isStoppingTime
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T07:55:33.637231+00:00
-- url     : https://prove2.me/submissions/61250712-75dd-4c54-adce-26a9da9f7c06

import Mathlib.Probability.Process.Adapted
import Mathlib.Topology.Semicontinuity.Basic
import Theorems.Thm_AvramDividend_Classical_runningSup_monotone_and_path_le
import Theorems.Thm_AvramDividend_Classical_runningSup_continuous_actual
import Theorems.Thm_AvramDividend_Classical_monotone_usc_capped_superlevel_isStoppingTime
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_adapted
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_self_eq_runningSup

open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (H : ℝ≥0) (a : ℝ) :
    IsStoppingTime 𝓕 (fun ω : Ω =>
      WithTop.some (sInf ((Icc (0 : ℝ≥0) H ∩
        (fun t : ℝ≥0 => runningSup X t ω) ⁻¹' Ici a) ∪ {H}))) := by
  have hfun : barrierStrategy X 0 0 = fun t ω => runningSup X t ω := by
    funext t ω; exact barrierStrategy_self_eq_runningSup X 0 ω t
  have hu : Adapted 𝓕 (fun t ω => runningSup X t ω) := hfun ▸ barrierStrategy_adapted X 0
  exact monotone_usc_capped_superlevel_isStoppingTime (fun t ω => runningSup X t ω) hu
    (fun ω => (runningSup_monotone_and_path_le X ω).1)
    (fun ω H => (runningSup_continuous_actual X ω).upperSemicontinuous.upperSemicontinuousOn _) H a
