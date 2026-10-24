-- Prove2me | solution 1 for FunctionalInequalities.Energy.PreEnergy.sequentialRelaxation_ofLinearPMap_le_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:54:38.24498+00:00
-- url     : https://prove2.me/submissions/720cf411-8dec-4e19-ac7a-41fdaed5c4bf

import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_Functional
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_QuadraticPreEnergy
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Relaxation_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Relaxation_LinearPMap
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Inv
import Mathlib.Topology.Algebra.Module.LinearPMap
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Order.LiminfLimsup

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
open Filter Topology Set
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Energy
end FunctionalInequalities.Energy
open FunctionalInequalities FunctionalInequalities.Energy
section PreEnergy
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
section
namespace FunctionalInequalities.Energy.PreEnergy
end FunctionalInequalities.Energy.PreEnergy
open FunctionalInequalities FunctionalInequalities.Energy FunctionalInequalities.Energy.PreEnergy
variable (T : X →ₗ.[ℝ] H)
namespace FunctionalInequalities.Energy.PreEnergy
end FunctionalInequalities.Energy.PreEnergy
open FunctionalInequalities.Energy.PreEnergy in
omit [CompleteSpace H] in
/-- The relaxed energy is at most `‖T̄ x‖²` on the domain of the closure. -/
theorem solution (hT : T.IsClosable) (x : T.closure.domain) :
    (FunctionalInequalities.Energy.PreEnergy.ofLinearPMap T).sequentialRelaxation x ≤ (‖T.closure x‖₊ ^ 2 : NNReal) := by
  have hmem : ((x : X), T.closure x) ∈ T.graph.topologicalClosure := by
    rw [hT.graph_closure_eq_closure_graph]
    exact T.closure.mem_graph x
  obtain ⟨f, hf⟩ := (FunctionalInequalities.Energy.mem_graph_topologicalClosure_iff T _).mp hmem
  have h1 : Tendsto (fun n ↦ (FunctionalInequalities.Energy.PreEnergy.ofLinearPMap T).toAmbient (f n)) atTop (𝓝 (x : X)) :=
    (continuous_fst.tendsto _).comp hf
  have h2 : Tendsto (fun n ↦ ((FunctionalInequalities.Energy.PreEnergy.ofLinearPMap T).energy (f n) : ENNReal)) atTop
      (𝓝 ((‖T.closure x‖₊ ^ 2 : NNReal) : ENNReal)) := by
    have h3 : Tendsto (fun n ↦ T (f n)) atTop (𝓝 (T.closure x)) :=
      (continuous_snd.tendsto _).comp hf
    have h4 : Tendsto (fun n ↦ ‖T (f n)‖₊ ^ 2) atTop (𝓝 (‖T.closure x‖₊ ^ 2)) :=
      (h3.nnnorm).pow 2
    exact (ENNReal.tendsto_coe.mpr h4)
  refine ((FunctionalInequalities.Energy.PreEnergy.ofLinearPMap T).sequentialRelaxation_le_sequenceEnergy ⟨f, h1⟩).trans_eq ?_
  exact h2.liminf_eq
