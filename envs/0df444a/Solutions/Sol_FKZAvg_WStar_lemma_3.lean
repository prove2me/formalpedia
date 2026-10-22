-- Prove2me | solution 1 for FKZAvg.WStar.lemma_3
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-21T14:09:37.929098+00:00
-- url     : https://prove2.me/submissions/888cfeaf-42a9-49ab-b76f-4e79b0fc96d1

import Mathlib
import Definitions.Def_FeinbergLiang_ACOE_MDP
import Definitions.Def_SchalAvg_AvgOpt_Model
import Definitions.Def_FKZAvg_WStar_Assumptions
open scoped ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Filter SchalAvg.AvgOpt
open FKZAvg.WStar

noncomputable def g70op_N : Model ℝ ℝ where
  toMDP := { lower := 0, cost := fun _ _ => 0,
             q := ProbabilityTheory.Kernel.const _ (Measure.dirac 1) }
  lower_eq := rfl
  Aset := fun _ => {0}
  Aset_nonempty := fun _ => ⟨0, rfl⟩
  graph_meas := measurable_snd (measurableSet_singleton 0)
  cost_meas := measurable_const

open Classical in
noncomputable def g70op_u : ℝ → ℝ≥0∞ := fun y => if y = 0 then 0 else ⊤

theorem g70op_hW : CondWStar g70op_N := by
  refine ⟨?_, ?_, ?_⟩
  · exact lowerSemicontinuousOn_const
  · intro xs x as _ has _
    have : as = fun _ => 0 := funext fun n => has n
    subst this
    exact ⟨0, rfl, by
      rw [mapClusterPt_iff_frequently]; intro s hs
      exact Frequently.of_forall fun _ => mem_of_mem_nhds hs⟩
  · intro f
    simp only [g70op_N, ProbabilityTheory.Kernel.const_apply, integral_dirac]
    exact continuousOn_const

theorem g70op_uL : InL g70op_u := by
  refine ⟨fun x y hy => ?_, ⟨0, by simp [g70op_u]⟩⟩
  by_cases hx : x = 0
  · subst hx; simp [g70op_u] at hy
  · filter_upwards [isOpen_ne.mem_nhds hx] with z hz
    simpa [g70op_u, hz] using hy.trans_le le_top

theorem g70op_ustar (x : ℝ) : uStar g70op_N g70op_u x = ⊤ := by
  simp [uStar, eta, g70op_N, g70op_u, lintegral_dirac]

theorem solution : ¬ (∀ {X A : Type}
    [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X] [StandardBorelSpace X]
    [TopologicalSpace A] [TopologicalSpace.MetrizableSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A] [StandardBorelSpace A]
    (M : Model X A) (hsel : HasSelector M)
    (hW : CondWStar M) (u : X → ℝ≥0∞) (hu : InL u),
    InL (uStar M u) ∧
    (∃ f : X → A, IsStationary M f ∧ ∀ x, uStar M u x = eta M u 1 x (f x)) ∧
    (∀ x, (AsubStar M u x).Nonempty) ∧
    MeasurableSet {p : X × A | p.2 ∈ AsubStar M u p.1} ∧
    ∀ x, (uStar M u x = ⊤ → AsubStar M u x = M.Aset x) ∧
      (uStar M u x ≠ ⊤ → IsCompact (AsubStar M u x))) := by
  intro H
  have hsel : HasSelector g70op_N := ⟨fun _ => 0, measurable_const, fun _ => rfl⟩
  obtain ⟨x, hx⟩ := (H g70op_N hsel g70op_hW g70op_u g70op_uL).1.2
  exact hx (g70op_ustar x)
