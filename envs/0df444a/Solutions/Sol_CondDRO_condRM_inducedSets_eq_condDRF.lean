-- Prove2me | solution 1 for CondDRO.condRM_inducedSets_eq_condDRF
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T03:39:52.430694+00:00
-- url     : https://prove2.me/submissions/0c9764f5-1080-4b86-9131-fd052d4cfcee

import Mathlib
import Definitions.Def_CondDRO_FinitePartition
import Definitions.Def_CondDRO_condDRF
import Definitions.Def_CondDRO_condRM
import Definitions.Def_CondDRO_inducedSets

open MeasureTheory

open CondDRO in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {I : Type*} [Fintype I]
    (ϖ : FinitePartition Ω I) (M : Set (Measure Ω))
    (hM_prob : ∀ Q ∈ M, IsProbabilityMeasure Q)
    (hM_assum : ∀ i, ∃ Q ∈ M, Q (ϖ.cell i) ≠ 0)
    (Z : Ω → ℝ) (hZ_meas : Measurable Z) (hZ_int : ∀ Q ∈ M, Integrable Z Q) :
    condRM (inducedSets M ϖ) Z = condDRF M ϖ Z := by
  funext i
  unfold condRM inducedSets condDRF
  rw [iSup_image]
  refine iSup_congr (fun Q => iSup_congr (fun _ => ?_))
  congr 1
  rw [ProbabilityTheory.cond, integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul]
