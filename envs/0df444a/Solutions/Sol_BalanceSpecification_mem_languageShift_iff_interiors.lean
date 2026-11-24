-- Prove2me | solution 1 for BalanceSpecification.mem_languageShift_iff_interiors
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:41:31.661369+00:00
-- url     : https://prove2.me/submissions/ff59adaf-b731-4d9c-b75e-3df3399dc59c

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
public import Theorems.Thm_BalanceSpecification_mem_languageShift_of_arbitrary_contexts
public import Theorems.Thm_BalanceSpecification_mem_interiors_of_mem_languageShift

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
    {L : Set (Word A)} (hL : IsFactorial L) {w : Word A} :
    w ∈ language (languageShift L) ↔ ∀ M, w ∈ interiorLanguage L M := by
  constructor
  · exact mem_interiors_of_mem_languageShift
  · exact mem_languageShift_of_arbitrary_contexts hL
end BalanceSpecification
