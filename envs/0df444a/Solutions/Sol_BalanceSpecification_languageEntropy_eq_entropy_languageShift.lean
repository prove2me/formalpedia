-- Prove2me | solution 1 for BalanceSpecification.languageEntropy_eq_entropy_languageShift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:57:34.513038+00:00
-- url     : https://prove2.me/submissions/5a38a4a1-56e9-4fec-934e-da2449254c06

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
public import Theorems.Thm_BalanceSpecification_languageEntropy_language_eq_entropy
public import Theorems.Thm_BalanceSpecification_languageEntropy_eq_languageShift

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
theorem _root_.solution {L : Set (Word A)}
    (hL : IsFactorial L) (hX : (languageShift L).carrier.Nonempty) :
    languageEntropy L = (entropy (languageShift L) hX : EReal) := by
  rw [languageEntropy_eq_languageShift hL, languageEntropy_language_eq_entropy hX]
end BalanceSpecification
