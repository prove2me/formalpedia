-- Prove2me | solution 1 for BalanceSpecification.languageEntropy_language_eq_entropy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:55:08.230862+00:00
-- url     : https://prove2.me/submissions/e8f3d79e-5378-4685-baee-e7351c4fca9c

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
public import Theorems.Thm_BalanceSpecification_languageEntropy_eq_rate
public import Theorems.Thm_BalanceSpecification_language_factorial
public import Theorems.Thm_BalanceSpecification_wordCount_pos_of_nonempty


set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open scoped ENNReal
open BalanceSpecification
variable {A : Type*}
variable [TopologicalSpace A] [DiscreteTopology A]
variable [Fintype A]
omit [DiscreteTopology A]
namespace BalanceSpecification
theorem _root_.solution {X : ShiftSpace A}
    (hX : X.carrier.Nonempty) : languageEntropy (language X) = (entropy X hX : EReal) :=
  languageEntropy_eq_rate (language_factorial X) (wordCount_pos_of_nonempty hX)
end BalanceSpecification
