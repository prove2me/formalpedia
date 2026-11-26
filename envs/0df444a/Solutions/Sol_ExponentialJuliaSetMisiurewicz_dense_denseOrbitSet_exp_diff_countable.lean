-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.dense_denseOrbitSet_exp_diff_countable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:17:38.980449+00:00
-- url     : https://prove2.me/submissions/c363ad7e-9259-48f6-a562-a85a5c6247ba

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
theorem _root_.solution {C : Set ℂ} (hC : C.Countable) :
    Dense (denseOrbitSetExp \ C) := by
  let _ : Countable (TopologicalSpace.countableBasis ℂ) :=
    (TopologicalSpace.countable_countableBasis ℂ).to_subtype
  let _ : Countable C := hC.to_subtype
  let A := (TopologicalSpace.countableBasis ℂ) ⊕ C
  let G : A → Set ℂ := fun a => match a with
    | Sum.inl U => orbitVisitSet U
    | Sum.inr z => ({(z : ℂ)} : Set ℂ)ᶜ
  have hGopen : ∀ a, IsOpen (G a) := by
    rintro (U | z)
    · exact (isOpen_dense_orbitVisitSet
        (TopologicalSpace.isOpen_of_mem_countableBasis U.2)
        (Set.nonempty_iff_ne_empty.mpr fun hU =>
          TopologicalSpace.empty_notMem_countableBasis ℂ (hU ▸ U.2))).1
    · exact isOpen_compl_singleton
  have hGdense : ∀ a, Dense (G a) := by
    rintro (U | z)
    · exact (isOpen_dense_orbitVisitSet
        (TopologicalSpace.isOpen_of_mem_countableBasis U.2)
        (Set.nonempty_iff_ne_empty.mpr fun hU =>
          TopologicalSpace.empty_notMem_countableBasis ℂ (hU ▸ U.2))).2
    · change Dense ({(z : ℂ)}ᶜ : Set ℂ)
      exact dense_compl_singleton (z : ℂ)
  apply (dense_iInter_of_isOpen hGopen hGdense).mono
  intro z hz
  constructor
  · rw [mem_denseOrbitSetExp_iff_visit_countableBasis, mem_iInter]
    intro U
    exact mem_iInter.mp hz (Sum.inl U)
  · intro hzC
    have hzcompl := mem_iInter.mp hz (Sum.inr (⟨z, hzC⟩ : C))
    exact hzcompl (by simp)
end ExponentialJuliaSetMisiurewicz
