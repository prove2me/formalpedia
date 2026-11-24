-- Prove2me | solution 1 for BalanceSpecification.measureEntropy_eq_sInf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:12:49.368026+00:00
-- url     : https://prove2.me/submissions/5627cb44-bec1-414a-875d-4d982a88eb3e

module
public import Definitions.Def_BalanceSpecificaton_Measures
public import Definitions.Def_BalanceSpecificaton_EntropyAlgebra
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_BlockEntropy

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
    measureEntropy μ hInv =
      sInf ((fun n : ℕ => blockEntropy μ n / n) '' Set.Ici 1) := by
  rw [measureEntropy, Subadditive.lim]
end BalanceSpecification
