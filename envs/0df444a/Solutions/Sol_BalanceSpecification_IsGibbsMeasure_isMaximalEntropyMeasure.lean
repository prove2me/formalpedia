-- Prove2me | solution 1 for BalanceSpecification.IsGibbsMeasure.isMaximalEntropyMeasure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:15:33.459413+00:00
-- url     : https://prove2.me/submissions/b4a2330d-309d-4023-b19c-67a72f6ca655

module
public import Definitions.Def_BalanceSpecificaton_BlockEntropy
public import Definitions.Def_BalanceSpecificaton_GibbsExistence
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_MaximalEntropy
public import Theorems.Thm_BalanceSpecification_GibbsBounds_measureEntropy_eq_entropy

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
namespace IsGibbsMeasure
theorem _root_.solution {hX : X.carrier.Nonempty}
    {μ : ProbabilityMeasure X.carrier} (hG : IsGibbsMeasure hX μ) :
    IsMaximalEntropyMeasure hX μ := by
  obtain ⟨K, hB⟩ := hG.2
  exact ⟨hG.1, hB.measureEntropy_eq_entropy hG.1⟩
end IsGibbsMeasure
end BalanceSpecification
