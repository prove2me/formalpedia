-- Prove2me | solution 1 for BalanceSpecification.measureEntropy_le_blockEntropy_div
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:12:53.878214+00:00
-- url     : https://prove2.me/submissions/c6fb391f-971f-40e0-8dd0-70e7f30a1448

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
theorem _root_.solution {μ : ProbabilityMeasure X.carrier}
    (hInv : IsInvariant μ) {n : ℕ} (hn : n ≠ 0) :
    measureEntropy μ hInv ≤ blockEntropy μ n / n :=
  (blockEntropy_subadditive hInv).lim_le_div (blockEntropy_normalized_bddBelow μ) hn
end BalanceSpecification
