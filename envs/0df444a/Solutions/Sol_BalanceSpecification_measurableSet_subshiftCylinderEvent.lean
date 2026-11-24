-- Prove2me | solution 1 for BalanceSpecification.measurableSet_subshiftCylinderEvent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:51:50.410625+00:00
-- url     : https://prove2.me/submissions/e742eb83-9409-4483-bfce-a5eaf1937744

module
public import Definitions.Def_BalanceSpecificaton_CylinderAlgebra
public import Definitions.Def_BalanceSpecificaton_EntropyMinimal
public import Mathlib.Dynamics.Ergodic.Ergodic
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_GibbsEntropyMinimal
public import Theorems.Thm_BalanceSpecification_measurableSet_cylinder


set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
open BalanceSpecification
variable {A : Type*} [TopologicalSpace A]
variable [Fintype A]
variable [DiscreteTopology A] [MeasurableSpace A] [BorelSpace A]
namespace BalanceSpecification
theorem _root_.solution (X Y : ShiftSpace A) (n : ℕ) :
    MeasurableSet (subshiftCylinderEvent X Y n) :=
  (wordFinset (language Y) (2 * n + 1)).measurableSet_biUnion
    (fun w _ => measurableSet_cylinder X w _)
end BalanceSpecification
