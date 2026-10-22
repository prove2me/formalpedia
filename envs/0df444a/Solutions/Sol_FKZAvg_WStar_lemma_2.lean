-- Prove2me | solution 1 for FKZAvg.WStar.lemma_2
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-21T12:56:00.985067+00:00
-- url     : https://prove2.me/submissions/58c1e393-cc4e-44e7-b49b-56d6053bd574

import Mathlib
import Definitions.Def_FeinbergLiang_ACOE_MDP
import Definitions.Def_SchalAvg_AvgOpt_Model
import Definitions.Def_FKZAvg_WStar_Assumptions
open scoped ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Filter SchalAvg.AvgOpt
open FKZAvg.WStar

open Classical in
noncomputable def g69h2_M : Model Unit ℝ where
  toMDP := { lower := 0, cost := fun _ a => if a = 0 then 1 else 0,
             q := ProbabilityTheory.Kernel.const _ (Measure.dirac ()) }
  lower_eq := rfl
  Aset := fun _ => Set.Icc 0 1
  Aset_nonempty := fun _ => ⟨0, by simp⟩
  graph_meas := measurable_snd measurableSet_Icc
  cost_meas := by
    apply Measurable.ite _ measurable_const measurable_const
    exact measurable_snd (measurableSet_singleton 0)

theorem g69h2_hsel : HasSelector g69h2_M :=
  ⟨fun _ => 1, measurable_const, fun _ => by simp [g69h2_M]⟩

theorem g69h2_ii : CondWStar_ii g69h2_M := by
  intro xs x as _ has _
  have hc : IsCompact (Set.Icc (0:ℝ) 1) := isCompact_Icc
  obtain ⟨a, ha, hcl⟩ := hc.exists_mapClusterPt_of_frequently (l := atTop) (f := as)
    (Frequently.of_forall fun n => has n)
  exact ⟨a, ha, hcl⟩

theorem g69h2_not_ic : ¬ InfCompactOn (fun a => g69h2_M.toMDP.cost () a) (g69h2_M.Aset ()) := by
  intro h
  have hK := (h 0).isClosed
  have hmem : (0:ℝ) ∈ {y | y ∈ g69h2_M.Aset () ∧ g69h2_M.toMDP.cost () y ≤ ((0 : ℝ≥0) : ℝ≥0∞)} := by
    apply hK.mem_of_tendsto (f := fun n : ℕ => 1 / ((n:ℝ) + 2)) (b := atTop)
    · have h2 : Tendsto (fun n : ℕ => (n:ℝ) + 2) atTop atTop :=
        tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
      exact (tendsto_const_nhds (x := (1:ℝ))).div_atTop h2
    · refine Eventually.of_forall fun n => ?_
      have hp : (0:ℝ) < 1 / ((n:ℝ) + 2) := by positivity
      have hle : 1 / ((n:ℝ) + 2) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith [(n.cast_nonneg : (0:ℝ) ≤ n)]
      have hn : (0:ℝ) ≤ n := n.cast_nonneg
      simp [g69h2_M]
      refine ⟨⟨by positivity, ?_⟩, by positivity⟩
      rw [inv_le_one₀ (by positivity)]; linarith
  simp [g69h2_M] at hmem

theorem solution : ¬ (∀ {X A : Type}
    [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X] [StandardBorelSpace X]
    [TopologicalSpace A] [TopologicalSpace.MetrizableSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A] [StandardBorelSpace A]
    (M : Model X A) (hsel : HasSelector M) (x : X),
    (CondWStar_ii M → InfCompactOn (fun a => M.toMDP.cost x a) (M.Aset x)) ∧
    (CondWStar_ii M → CondWStar_iii M →
      ∀ u : X → ℝ≥0∞, InL u → ∀ α : ℝ, 0 ≤ α →
        InfCompactOn (fun a => eta M u α x a) (M.Aset x))) := by
  intro H
  exact g69h2_not_ic ((H g69h2_M g69h2_hsel ()).1 g69h2_ii)
