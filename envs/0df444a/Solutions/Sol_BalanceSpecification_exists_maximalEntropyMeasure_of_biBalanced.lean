-- Prove2me | solution 1 for BalanceSpecification.exists_maximalEntropyMeasure_of_biBalanced
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:18:31.368954+00:00
-- url     : https://prove2.me/submissions/76aa3bfe-1554-422e-9b3e-7bdb43ac5079

module
public import Definitions.Def_BalanceSpecificaton_BlockEntropy
public import Definitions.Def_BalanceSpecificaton_GibbsExistence
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_MaximalEntropy
public import Theorems.Thm_BalanceSpecification_IsGibbsMeasure_isMaximalEntropyMeasure
public import Theorems.Thm_BalanceSpecification_exists_invariantGibbs_of_biBalanced


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
    (hB : BiBalanced (language X)) :
    ∃ μ : ProbabilityMeasure X.carrier, IsMaximalEntropyMeasure hX μ := by
  obtain ⟨μ, hG⟩ := exists_invariantGibbs_of_biBalanced hX hB
  exact ⟨μ, hG.isMaximalEntropyMeasure⟩
end BalanceSpecification
