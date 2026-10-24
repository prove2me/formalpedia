-- Prove2me | solution 1 for FunctionalInequalities.Energy.PreEnergy.lowerSemicontinuous_sequentialRelaxation_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:54:24.766976+00:00
-- url     : https://prove2.me/submissions/19df9d30-cec1-4725-90ed-26a98ffca519

import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_Functional
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Relaxation_Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Inv
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Theorems.Thm_FunctionalInequalities_Energy_PreEnergy_exists_test_near_of_relaxation_lt_408915f

section
noncomputable section
open Filter Topology
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Energy
end FunctionalInequalities.Energy
open FunctionalInequalities FunctionalInequalities.Energy
universe u v
section
namespace FunctionalInequalities.Energy.PreEnergy
end FunctionalInequalities.Energy.PreEnergy
open FunctionalInequalities FunctionalInequalities.Energy FunctionalInequalities.Energy.PreEnergy
variable {X : Type u} [TopologicalSpace X] (P : PreEnergy X)
/-- Every particular approximating sequence gives an upper bound for the relaxed energy. -/
theorem FunctionalInequalities.Energy.PreEnergy.sequentialRelaxation_le_sequenceEnergy {x : X} (f : P.ApproximatingSequence x) :
    P.sequentialRelaxation x ≤ P.sequenceEnergy f :=
  iInf_le _ f
end
end
end
end
end

noncomputable section
open Filter Topology
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Energy
end FunctionalInequalities.Energy
open FunctionalInequalities FunctionalInequalities.Energy
section
namespace FunctionalInequalities.Energy.PreEnergy
end FunctionalInequalities.Energy.PreEnergy
open FunctionalInequalities FunctionalInequalities.Energy FunctionalInequalities.Energy.PreEnergy
section Semicontinuity
universe u
variable {X : Type u} [PseudoMetricSpace X] (P : PreEnergy X)
namespace FunctionalInequalities.Energy.PreEnergy
end FunctionalInequalities.Energy.PreEnergy
open FunctionalInequalities.Energy.PreEnergy in
/-- Sequential relaxation is lower semicontinuous in a pseudometric ambient space. -/
theorem solution :
    LowerSemicontinuous (fun x ↦ P.sequentialRelaxation x) := by
  apply LowerSemicontinuous.of_frequently
  intro x bound hfrequent
  by_cases hbound : bound = ⊤
  · simp [hbound]
  obtain ⟨xseq, hxseq, hxseq_bound⟩ := exists_seq_forall_of_frequently hfrequent
  let metricError : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1)
  let energyError : ℕ → ENNReal := fun n ↦ ((n : NNReal) : ENNReal)⁻¹
  have metricError_pos : ∀ n, 0 < metricError n := by
    intro n
    dsimp [metricError]
    positivity
  have energyError_pos : ∀ n, 0 < energyError n := by
    intro n
    simp [energyError]
  have exists_test : ∀ n, ∃ f : P.Test,
      dist (P.toAmbient f) (xseq n) < metricError n ∧
        (P.energy f : ENNReal) < bound + energyError n := by
    intro n
    have hrelaxed : P.sequentialRelaxation (xseq n) < bound + energyError n :=
      (hxseq_bound n).trans_lt
        (ENNReal.lt_add_right hbound (energyError_pos n).ne')
    exact P.exists_test_near_of_relaxation_lt_408915f hrelaxed (metricError_pos n)
  choose test htest_near htest_energy using exists_test
  have metricError_tendsto : Tendsto metricError atTop (𝓝 0) := by
    simpa [metricError] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hdist :
      Tendsto (fun n ↦ dist (xseq n) (P.toAmbient (test n))) atTop (𝓝 0) := by
    apply Filter.Tendsto.squeeze tendsto_const_nhds metricError_tendsto
    · intro n
      exact dist_nonneg
    · intro n
      simpa [dist_comm] using (htest_near n).le
  have htest_tendsto : Tendsto (fun n ↦ P.toAmbient (test n)) atTop (𝓝 x) :=
    tendsto_of_tendsto_of_dist hxseq hdist
  let approximation : P.ApproximatingSequence x := ⟨test, htest_tendsto⟩
  have energyError_tendsto : Tendsto energyError atTop (𝓝 0) := by
    simpa [energyError] using ENNReal.tendsto_inv_nat_nhds_zero
  calc
    P.sequentialRelaxation x ≤ P.sequenceEnergy approximation :=
      P.sequentialRelaxation_le_sequenceEnergy approximation
    _ ≤ liminf (fun n ↦ bound + energyError n) atTop :=
      liminf_le_liminf (Eventually.of_forall fun n ↦ (htest_energy n).le)
    _ = bound := by
      simpa using (tendsto_const_nhds.add energyError_tendsto).liminf_eq
