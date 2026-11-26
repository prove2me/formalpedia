-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.isOpen_dense_orbitVisitSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:16:57.1078+00:00
-- url     : https://prove2.me/submissions/e61721b6-d1fe-4bce-80bb-902056478e1b

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
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_continuous_expIterate
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_exists_iterate_eq_nonzero
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_exists_nonzero_mem_open
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_expIterate_succ
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_expIterate_zero
attribute [local simp] ExponentialJuliaSetMisiurewicz.expIterate_succ
attribute [local simp] ExponentialJuliaSetMisiurewicz.expIterate_zero



set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section
namespace ExponentialJuliaSetMisiurewicz
theorem _root_.solution {U : Set ℂ} (hU : IsOpen U) (hUne : U.Nonempty) :
    IsOpen (orbitVisitSet U) ∧ Dense (orbitVisitSet U) := by
  constructor
  · exact isOpen_iUnion fun n => hU.preimage (continuous_expIterate n)
  · apply dense_iff_inter_open.mpr
    intro V hV hVne
    obtain ⟨w, hwU, hw0⟩ := exists_nonzero_mem_open hU hUne
    obtain ⟨n, _, z, hzV, hzw⟩ := exists_iterate_eq_nonzero hV hVne hw0
    refine ⟨z, hzV, ?_⟩
    exact mem_iUnion.2 ⟨n, by simpa [hzw] using hwU⟩
end ExponentialJuliaSetMisiurewicz
