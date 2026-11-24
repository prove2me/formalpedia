-- Prove2me | solution 1 for BalanceSpecification.blockEntropy_normalized_bddBelow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:10:47.235649+00:00
-- url     : https://prove2.me/submissions/37e70192-199c-4198-aa6b-0708332301c5

module
public import Definitions.Def_BalanceSpecificaton_Measures
public import Definitions.Def_BalanceSpecificaton_EntropyAlgebra
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_BlockEntropy
public import Theorems.Thm_BalanceSpecification_blockEntropy_nonneg

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
open MeasureTheory Filter
open scoped Topology
variable {A : Type*} [Fintype A] [TopologicalSpace A] [DiscreteTopology A]
  [MeasurableSpace A] [BorelSpace A] {X : ShiftSpace A}
omit [DiscreteTopology A] [BorelSpace A]
namespace BalanceSpecification
theorem _root_.solution (μ : ProbabilityMeasure X.carrier) :
    BddBelow (Set.range fun n : ℕ => blockEntropy μ n / n) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨n, rfl⟩
  exact div_nonneg (blockEntropy_nonneg μ n) (Nat.cast_nonneg n)
end BalanceSpecification
