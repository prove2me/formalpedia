-- Prove2me | solution 1 for BalanceSpecification.exists_centered_block_realization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:13:50.369281+00:00
-- url     : https://prove2.me/submissions/b99fd4b4-c2bd-43ec-9ab9-686d299c56b0

module
public import Definitions.Def_BalanceSpecificaton_CylinderAlgebra
public import Definitions.Def_BalanceSpecificaton_EntropyMinimal
public import Mathlib.Dynamics.Ergodic.Ergodic
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_GibbsEntropyMinimal
public import Theorems.Thm_BalanceSpecification_block_shift
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_mem_language_iff_exists_block_zero
attribute [local simp] BalanceSpecification.length_block



set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
open BalanceSpecification
variable {A : Type*} [TopologicalSpace A]
namespace BalanceSpecification
theorem _root_.solution {Y : ShiftSpace A} {x : Configuration A} {n : ℕ}
    (h : block x (-(n : ℤ)) (2 * n + 1) ∈ language Y) :
    ∃ y ∈ Y.carrier, block y (-(n : ℤ)) (2 * n + 1) =
      block x (-(n : ℤ)) (2 * n + 1) := by
  obtain ⟨y, hy, hblock⟩ := mem_language_iff_exists_block_zero.mp h
  rw [length_block] at hblock
  refine ⟨SymbolicDynamics.FullShift.shift (n : ℤ) y, Y.mapsTo (n : ℤ) hy, ?_⟩
  rw [block_shift, add_neg_cancel]
  exact hblock
end BalanceSpecification
