-- Prove2me | solution 1 for FunctionalInequalities.Energy.PreEnergy.hasRecoverySequenceAt_sequentialRelaxation_of_finiteAt_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:53:44.636178+00:00
-- url     : https://prove2.me/submissions/667370da-35a7-4ad0-8ac2-fa9ce2f2e995

import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_Core
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_Functional
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Relaxation_Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Inv
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Order.LiminfLimsup
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
universe u
variable {X : Type u} [PseudoMetricSpace X] (P : PreEnergy X)
namespace FunctionalInequalities.Energy.PreEnergy
end FunctionalInequalities.Energy.PreEnergy
open FunctionalInequalities.Energy.PreEnergy in
/-- Every finite point of a sequential relaxation has a recovery sequence.

The proof chooses, for each precision, an approximating sequence whose `liminf` is nearly
minimal and then one sufficiently late concrete test from that sequence.
-/
theorem solution {x : X}
    (hfinite : P.sequentialRelaxation.FiniteAt x) :
    P.HasRecoverySequenceAt P.sequentialRelaxation x := by
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
      dist x (P.toAmbient f) < metricError n ∧
        (P.energy f : ENNReal) < P.sequentialRelaxation x + energyError n := by
    intro n
    have hrelaxed :
        P.sequentialRelaxation x < P.sequentialRelaxation x + energyError n :=
      ENNReal.lt_add_right hfinite (energyError_pos n).ne'
    simpa only [dist_comm] using
      P.exists_test_near_of_relaxation_lt_408915f hrelaxed (metricError_pos n)
  choose test htest_near htest_energy using exists_test
  have metricError_tendsto : Tendsto metricError atTop (𝓝 0) := by
    simpa [metricError] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hdist :
      Tendsto (fun n ↦ dist x (P.toAmbient (test n))) atTop (𝓝 0) := by
    apply Filter.Tendsto.squeeze tendsto_const_nhds metricError_tendsto
    · intro n
      exact dist_nonneg
    · intro n
      exact (htest_near n).le
  have htest_tendsto : Tendsto (fun n ↦ P.toAmbient (test n)) atTop (𝓝 x) :=
    tendsto_of_tendsto_of_dist tendsto_const_nhds hdist
  let approximation : P.ApproximatingSequence x := ⟨test, htest_tendsto⟩
  have energyError_tendsto : Tendsto energyError atTop (𝓝 0) := by
    simpa [energyError] using ENNReal.tendsto_inv_nat_nhds_zero
  have hupper_tendsto :
      Tendsto (fun n ↦ P.sequentialRelaxation x + energyError n) atTop
        (𝓝 (P.sequentialRelaxation x)) := by
    simpa using (tendsto_const_nhds.add energyError_tendsto)
  have hlower :
      P.sequentialRelaxation x ≤
        liminf (fun n ↦ (P.energy (test n) : ENNReal)) atTop :=
    P.sequentialRelaxation_le_sequenceEnergy approximation
  have hupper :
      limsup (fun n ↦ (P.energy (test n) : ENNReal)) atTop ≤
        P.sequentialRelaxation x := by
    refine (limsup_le_limsup (Eventually.of_forall fun n ↦ (htest_energy n).le)).trans_eq ?_
    exact hupper_tendsto.limsup_eq
  exact ⟨approximation, tendsto_of_le_liminf_of_limsup_le hlower hupper⟩
