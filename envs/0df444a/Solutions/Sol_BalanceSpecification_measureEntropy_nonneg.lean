-- Prove2me | solution 1 for BalanceSpecification.measureEntropy_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:18:25.437795+00:00
-- url     : https://prove2.me/submissions/f58841c3-79c4-4383-a227-8a953e0770b7

module
public import Definitions.Def_BalanceSpecificaton_Measures
public import Definitions.Def_BalanceSpecificaton_EntropyAlgebra
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_BlockEntropy
public import Theorems.Thm_BalanceSpecification_blockEntropy_nonneg
public import Theorems.Thm_BalanceSpecification_tendsto_measureEntropy

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
theorem _root_.solution {μ : ProbabilityMeasure X.carrier} (hInv : IsInvariant μ) :
    0 ≤ measureEntropy μ hInv := by
  apply ge_of_tendsto' (tendsto_measureEntropy hInv)
  intro n
  exact div_nonneg (blockEntropy_nonneg μ n) (Nat.cast_nonneg n)
end BalanceSpecification
