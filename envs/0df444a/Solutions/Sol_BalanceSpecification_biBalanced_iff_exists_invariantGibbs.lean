-- Prove2me | solution 1 for BalanceSpecification.biBalanced_iff_exists_invariantGibbs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:18:32.938331+00:00
-- url     : https://prove2.me/submissions/e7843e97-36f5-404e-815f-4cc5eedd04ee

module
public import Definitions.Def_BalanceSpecificaton_GibbsExistence
public import Definitions.Def_BalanceSpecificaton_BlockEntropy
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_GibbsBalance
public import Theorems.Thm_BalanceSpecification_biBalanced_of_isGibbsMeasure
public import Theorems.Thm_BalanceSpecification_exists_invariantGibbs_of_biBalanced


set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
open MeasureTheory
variable {A : Type*} [Fintype A] [TopologicalSpace A] [DiscreteTopology A]
  [MeasurableSpace A] [BorelSpace A] {X : ShiftSpace A}
namespace BalanceSpecification
theorem _root_.solution (hX : X.carrier.Nonempty) :
    BiBalanced (language X) ↔ ∃ μ : ProbabilityMeasure X.carrier, IsGibbsMeasure hX μ :=
  ⟨exists_invariantGibbs_of_biBalanced hX, fun ⟨_, hG⟩ => biBalanced_of_isGibbsMeasure hG⟩
end BalanceSpecification
