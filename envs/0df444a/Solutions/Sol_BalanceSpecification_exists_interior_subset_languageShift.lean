-- Prove2me | solution 1 for BalanceSpecification.exists_interior_subset_languageShift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:43:27.552694+00:00
-- url     : https://prove2.me/submissions/492f88bf-f544-4515-99bc-578d3e3b6495

module
public import Definitions.Def_BalanceSpecificaton_Forbidden
public import Definitions.Def_BalanceSpecificaton_Counting
public import Definitions.Def_BalanceSpecificaton_TilingBounds
public import Definitions.Def_BalanceSpecificaton_Entropy
public import Definitions.Def_BalanceSpecificaton_GrowthTiling
public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
public import Mathlib.Topology.Instances.EReal.Lemmas
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_FactorialEntropy
public import Theorems.Thm_BalanceSpecification_mem_languageShift_iff_interiors
public import Theorems.Thm_BalanceSpecification_interiorLanguage_antitone
public import Theorems.Thm_BalanceSpecification_mem_allWords
attribute [local simp] BalanceSpecification.mem_allWords



set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open scoped ENNReal
open BalanceSpecification
variable {A : Type*}
variable [TopologicalSpace A] [DiscreteTopology A]
variable [Fintype A]
namespace BalanceSpecification
theorem _root_.solution [Nonempty A]
    {L : Set (Word A)} (hL : IsFactorial L) (n : ℕ) :
    ∃ M : ℕ, ∀ w ∈ interiorLanguage L M, w.length = n →
      w ∈ language (languageShift L) := by
  classical
  have hevent : ∀ w ∈ allWords (A := A) n,
      ∀ᶠ M in Filter.atTop, w ∈ interiorLanguage L M → w ∈ language (languageShift L) := by
    intro w hw
    by_cases hcore : w ∈ language (languageShift L)
    · exact Filter.Eventually.of_forall fun _ _ => hcore
    · have hnot : ¬ ∀ M, w ∈ interiorLanguage L M :=
        fun h => hcore ((mem_languageShift_iff_interiors hL).mpr h)
      obtain ⟨M, hM⟩ := not_forall.mp hnot
      exact (Filter.eventually_ge_atTop M).mono fun N hN hwN =>
        False.elim (hM (interiorLanguage_antitone hN hwN))
  obtain ⟨M, hM⟩ := Filter.Eventually.exists ((Filter.eventually_all_finset _).mpr hevent)
  refine ⟨M, ?_⟩
  intro w hw hwlen
  exact hM w (mem_allWords.mpr hwlen) hw
end BalanceSpecification
