-- Prove2me | solution 1 for BanditAlgorithm.measurable_gittinsRetirementValue_of_finite_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-31T05:09:01.8073+00:00
-- url     : https://prove2.me/submissions/b67b1c31-dcb9-41cc-b194-c6cb5c352049

import Theorems.Thm_BanditAlgorithm_measurable_gittinsFiniteRetirementValue
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

open MeasureTheory ProbabilityTheory Filter Topology
open BanditAlgorithm

theorem solution
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    (α γ : ℝ)
    (hconv : ∀ x,
      Tendsto (fun n ↦ gittinsFiniteRetirementValue P r α γ n x)
        atTop (𝓝 (gittinsRetirementValue P r α γ x))) :
    Measurable (gittinsRetirementValue P r α γ) := by
  apply measurable_of_tendsto_metrizable
  · exact measurable_gittinsFiniteRetirementValue P hr α γ
  · rw [tendsto_pi_nhds]
    exact hconv
