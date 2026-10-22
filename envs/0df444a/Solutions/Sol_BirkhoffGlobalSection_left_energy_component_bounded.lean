-- Prove2me | solution 1 for BirkhoffGlobalSection.left_energy_component_bounded
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-23T18:24:14.958332+00:00
-- url     : https://prove2.me/submissions/2fc831a7-f7ab-4910-98fc-109fc5088ef1

import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Bornology.Constructions
import Mathlib.Tactic.FinCases
import Theorems.Thm_BirkhoffGlobalSection_left_component_position_coordinates_bounded
import Theorems.Thm_BirkhoffGlobalSection_left_component_momentum_coordinates_bounded

open BirkhoffGlobalSection

theorem solution (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) :
    Bornology.IsBounded (leftEnergyComponent μ c) := by
  obtain ⟨Rz, hz⟩ := left_component_position_coordinates_bounded μ c hμ0 hμ1 hc
  obtain ⟨Rw, hw⟩ := left_component_momentum_coordinates_bounded μ c hμ0 hμ1 hc
  let R : ℝ := max Rz Rw
  have hcoord : ∀ s ∈ leftEnergyComponent μ c, ∀ i : Fin 4, |s i| ≤ R := by
    intro s hs i
    fin_cases i
    · exact (hz s hs).1.trans (le_max_left Rz Rw)
    · exact (hz s hs).2.trans (le_max_left Rz Rw)
    · exact (hw s hs).1.trans (le_max_right Rz Rw)
    · exact (hw s hs).2.trans (le_max_right Rz Rw)
  have hsubset : leftEnergyComponent μ c ⊆
      Set.pi Set.univ (fun _ : Fin 4 => Set.Icc (-R) R) := by
    intro s hs i hi
    exact abs_le.mp (hcoord s hs i)
  exact (Bornology.IsBounded.pi (fun _ : Fin 4 => Metric.isBounded_Icc (-R) R)).subset
    hsubset
