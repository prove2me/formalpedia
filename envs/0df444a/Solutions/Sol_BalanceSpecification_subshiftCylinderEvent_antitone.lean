-- Prove2me | solution 1 for BalanceSpecification.subshiftCylinderEvent_antitone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:51:30.023964+00:00
-- url     : https://prove2.me/submissions/3580c689-ff2e-4398-ac45-e1a262806f78

module
public import Definitions.Def_BalanceSpecificaton_CylinderAlgebra
public import Definitions.Def_BalanceSpecificaton_EntropyMinimal
public import Mathlib.Dynamics.Ergodic.Ergodic
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_GibbsEntropyMinimal
public import Theorems.Thm_BalanceSpecification_exists_centered_block_realization
public import Theorems.Thm_BalanceSpecification_mem_subshiftCylinderEvent
public import Theorems.Thm_BalanceSpecification_block_mem_language
public import Theorems.Thm_BalanceSpecification_centered_block_eq_of_le


set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
open BalanceSpecification
variable {A : Type*} [TopologicalSpace A]
variable [Fintype A]
namespace BalanceSpecification
theorem _root_.solution (X Y : ShiftSpace A) :
    Antitone (subshiftCylinderEvent X Y) := by
  intro n N hn x hx
  apply mem_subshiftCylinderEvent.mpr
  obtain ⟨y, hy, hblocks⟩ := exists_centered_block_realization (mem_subshiftCylinderEvent.mp hx)
  have he := centered_block_eq_of_le hn hblocks
  rw [← he]
  exact block_mem_language hy _ _
end BalanceSpecification
