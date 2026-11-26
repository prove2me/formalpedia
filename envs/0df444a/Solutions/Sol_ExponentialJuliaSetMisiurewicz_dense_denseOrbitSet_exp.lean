-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.dense_denseOrbitSet_exp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:17:38.49366+00:00
-- url     : https://prove2.me/submissions/8f903e15-70cc-44a7-a0fa-40b7d099d314

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
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_isOpen_dense_orbitVisitSet
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_mem_denseOrbitSetExp_iff_visit_countableBasis

set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section
namespace ExponentialJuliaSetMisiurewicz
theorem _root_.solution : Dense denseOrbitSetExp := by
  let _ : Countable (TopologicalSpace.countableBasis ℂ) :=
    (TopologicalSpace.countable_countableBasis ℂ).to_subtype
  apply (dense_iInter_of_isOpen (fun U : TopologicalSpace.countableBasis ℂ =>
    (isOpen_dense_orbitVisitSet
    (TopologicalSpace.isOpen_of_mem_countableBasis U.2)
    (Set.nonempty_iff_ne_empty.mpr fun hU =>
      TopologicalSpace.empty_notMem_countableBasis ℂ (hU ▸ U.2))).1) fun U =>
        (isOpen_dense_orbitVisitSet
          (TopologicalSpace.isOpen_of_mem_countableBasis U.2)
          (Set.nonempty_iff_ne_empty.mpr fun hU =>
            TopologicalSpace.empty_notMem_countableBasis ℂ (hU ▸ U.2))).2).mono
  intro z hz
  exact mem_denseOrbitSetExp_iff_visit_countableBasis.mpr hz
end ExponentialJuliaSetMisiurewicz
