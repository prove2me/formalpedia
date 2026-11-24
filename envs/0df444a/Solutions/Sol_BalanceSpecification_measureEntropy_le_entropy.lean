-- Prove2me | solution 1 for BalanceSpecification.measureEntropy_le_entropy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:13:13.381657+00:00
-- url     : https://prove2.me/submissions/d9809bd9-ffd9-451c-9171-9f84eded2724

module
public import Definitions.Def_BalanceSpecificaton_Measures
public import Definitions.Def_BalanceSpecificaton_EntropyAlgebra
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_BlockEntropy
public import Theorems.Thm_BalanceSpecification_blockEntropy_le_log_wordCount
public import Theorems.Thm_BalanceSpecification_tendsto_measureEntropy
public import Theorems.Thm_BalanceSpecification_tendsto_entropy


set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
open MeasureTheory Filter
open scoped Topology
variable {A : Type*} [Fintype A] [TopologicalSpace A] [DiscreteTopology A]
  [MeasurableSpace A] [BorelSpace A] {X : ShiftSpace A}
namespace BalanceSpecification
theorem _root_.solution (hX : X.carrier.Nonempty)
    {μ : ProbabilityMeasure X.carrier} (hInv : IsInvariant μ) :
    measureEntropy μ hInv ≤ entropy X hX := by
  apply le_of_tendsto_of_tendsto (tendsto_measureEntropy hInv) (tendsto_entropy hX)
  exact Filter.Eventually.of_forall fun n =>
    div_le_div_of_nonneg_right (blockEntropy_le_log_wordCount μ n) (Nat.cast_nonneg n)
end BalanceSpecification
