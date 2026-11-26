-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.mem_denseOrbitSetExp_iff_visit_countableBasis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:03:54.629397+00:00
-- url     : https://prove2.me/submissions/1277bf6a-46b4-4aa0-a40a-1102a86b2049

import Mathlib.Dynamics.Transitive
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.GroupTheory.GroupAction.IterateAct
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Definitions.Def_ExpChaotic_Periodic
import Definitions.Def_ExpChaotic_Dynamics

set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section
namespace ExponentialJuliaSetMisiurewicz
theorem _root_.solution {z : ℂ} :
    z ∈ denseOrbitSetExp ↔
      z ∈ ⋂ U : TopologicalSpace.countableBasis ℂ, orbitVisitSet U := by
  constructor
  · intro hz
    rw [mem_iInter]
    intro U
    obtain ⟨w, hwRange, hwU⟩ := hz.exists_mem_open
      (TopologicalSpace.isOpen_of_mem_countableBasis U.2)
      (Set.nonempty_iff_ne_empty.mpr fun hU =>
        TopologicalSpace.empty_notMem_countableBasis ℂ (hU ▸ U.2))
    obtain ⟨n, rfl⟩ := hwRange
    exact mem_iUnion.2 ⟨n.val, hwU⟩
  · intro hz
    apply (TopologicalSpace.isBasis_countableBasis ℂ).dense_iff.mpr
    intro U hUb hUne
    have hzU : z ∈ orbitVisitSet U := by
      rw [mem_iInter] at hz
      exact hz ⟨U, hUb⟩
    obtain ⟨n, hn⟩ := mem_iUnion.mp hzU
    exact ⟨expIterate n z, hn, ⟨n⟩, rfl⟩
end ExponentialJuliaSetMisiurewicz
