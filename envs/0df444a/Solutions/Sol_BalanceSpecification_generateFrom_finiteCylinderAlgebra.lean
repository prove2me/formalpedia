-- Prove2me | solution 1 for BalanceSpecification.generateFrom_finiteCylinderAlgebra
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:20:42.698469+00:00
-- url     : https://prove2.me/submissions/d9f77f37-11e7-4e03-895e-0e31872ab5af

module
public import Definitions.Def_BalanceSpecificaton_Measures
public import Mathlib.MeasureTheory.Measure.MeasuredSets
public import Mathlib.MeasureTheory.SetAlgebra
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_CylinderAlgebra
public import Theorems.Thm_BalanceSpecification_centeredCylinderFamily_subset_finiteCylinderAlgebra
public import Theorems.Thm_BalanceSpecification_measurableSet_of_mem_finiteCylinderAlgebra
public import Theorems.Thm_BalanceSpecification_generateFrom_centeredCylinderFamily

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MeasureTheory Set MeasurableSpace
open scoped symmDiff ENNReal
open BalanceSpecification
variable {A : Type*}
variable [TopologicalSpace A]
variable [Fintype A] [DiscreteTopology A] [MeasurableSpace A] [BorelSpace A]
namespace BalanceSpecification
theorem _root_.solution (X : ShiftSpace A) :
    (inferInstance : MeasurableSpace X.carrier) =
      MeasurableSpace.generateFrom (finiteCylinderAlgebra X) := by
  apply le_antisymm
  · rw [generateFrom_centeredCylinderFamily]
    exact generateFrom_mono (centeredCylinderFamily_subset_finiteCylinderAlgebra X)
  · exact generateFrom_le (fun _ h => measurableSet_of_mem_finiteCylinderAlgebra h)
end BalanceSpecification
