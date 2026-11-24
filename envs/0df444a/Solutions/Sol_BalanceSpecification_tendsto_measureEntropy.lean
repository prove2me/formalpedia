-- Prove2me | solution 1 for BalanceSpecification.tendsto_measureEntropy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:12:01.868116+00:00
-- url     : https://prove2.me/submissions/1164155b-8238-4e5c-898d-b53c7ab736fe

module
public import Definitions.Def_BalanceSpecificaton_Measures
public import Definitions.Def_BalanceSpecificaton_EntropyAlgebra
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_BlockEntropy
public import Theorems.Thm_BalanceSpecification_blockEntropy_normalized_bddBelow

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
    Tendsto (fun n : ℕ => blockEntropy μ n / n) atTop (𝓝 (measureEntropy μ hInv)) :=
  (blockEntropy_subadditive hInv).tendsto_lim (blockEntropy_normalized_bddBelow μ)
end BalanceSpecification
