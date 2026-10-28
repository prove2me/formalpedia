-- Prove2me | solution 1 for FunctionalInequalities.Energy.PreEnergy.sequentialRelaxation_ofLinearPMap_le_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:43:25.539268+00:00
-- url     : https://prove2.me/submissions/232f0746-a94a-4397-a8c7-99e1d0233565

import Definitions.Def_KLSModular_FunctionalInequalities_Energy_Relaxation_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_Energy_Relaxation_LinearPMap

section
noncomputable section
open Filter Topology
section
universe u v
section
variable {X : Type u} [TopologicalSpace X] (P : FunctionalInequalities.Energy.PreEnergy X)
/-- Every particular approximating sequence gives an upper bound for the relaxed energy. -/
theorem FunctionalInequalities.Energy.PreEnergy.sequentialRelaxation_le_sequenceEnergy {x : X} (f : P.ApproximatingSequence x) :
    P.sequentialRelaxation x ≤ P.sequenceEnergy f :=
  iInf_le _ f
end
end
end
end

noncomputable section
open Filter Topology Set
section PreEnergy
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (T : X →ₗ.[ℝ] H)
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
