-- Prove2me | solution 1 for BalanceSpecification.cylinder_preimage_iterate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:06:41.220253+00:00
-- url     : https://prove2.me/submissions/af01d3c0-7fab-42f8-b76c-78b2104d534d

module
public import Definitions.Def_BalanceSpecificaton_Periodicity
public import Definitions.Def_BalanceSpecificaton_Forbidden
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Measures
public import Theorems.Thm_BalanceSpecification_block_shift
public import Theorems.Thm_BalanceSpecification_shiftMap_iterate_val


set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MeasureTheory
open BalanceSpecification
variable {A : Type*} [TopologicalSpace A]
namespace BalanceSpecification
theorem _root_.solution (X : ShiftSpace A) (w : Word A) (k : ℤ) (n : ℕ) :
    (shiftMap X)^[n] ⁻¹' cylinder X w k = cylinder X w ((n : ℤ) + k) := by
  ext x
  change block ((shiftMap X)^[n] x).val k w.length = w ↔ _
  rw [shiftMap_iterate_val, block_shift]
  rfl
end BalanceSpecification
