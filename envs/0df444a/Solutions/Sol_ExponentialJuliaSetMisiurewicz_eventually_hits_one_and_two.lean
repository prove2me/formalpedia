-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.eventually_hits_one_and_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:16:18.213612+00:00
-- url     : https://prove2.me/submissions/f67c7e21-4ad2-43c8-b9af-e48143beeaee

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Topology.Compactification.OnePoint.Sphere
import Definitions.Def_ExpChaotic_Covering
import Definitions.Def_ExpChaotic_Spherical
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_eventually_hits_nonzero


set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section
namespace ExponentialJuliaSetMisiurewicz
theorem _root_.solution {U : Set ℂ} (hU : IsOpen U) (hUne : U.Nonempty) :
    ∃ N : ℕ, ∀ n ≥ N,
      (∃ z ∈ U, expIterate n z = 1) ∧ (∃ z ∈ U, expIterate n z = 2) := by
  obtain ⟨N₁, h₁⟩ := eventually_hits_nonzero hU hUne (w := 1) (by norm_num)
  obtain ⟨N₂, h₂⟩ := eventually_hits_nonzero hU hUne (w := 2) (by norm_num)
  exact ⟨max N₁ N₂, fun n hn =>
    ⟨h₁ n (le_trans (le_max_left _ _) hn), h₂ n (le_trans (le_max_right _ _) hn)⟩⟩
end ExponentialJuliaSetMisiurewicz
