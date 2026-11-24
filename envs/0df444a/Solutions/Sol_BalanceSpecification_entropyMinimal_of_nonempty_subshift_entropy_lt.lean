-- Prove2me | solution 1 for BalanceSpecification.entropyMinimal_of_nonempty_subshift_entropy_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:42:12.768021+00:00
-- url     : https://prove2.me/submissions/de61a2f8-fcad-42c7-aacd-e236aeb6566e

module
public import Definitions.Def_BalanceSpecificaton_FactorialEntropy
public import Definitions.Def_BalanceSpecificaton_Occurrence
public import Definitions.Def_BalanceSpecificaton_Synchronization
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_EntropyMinimal
public import Theorems.Thm_BalanceSpecification_languageEntropy_eq_bot_of_empty_carrier
public import Theorems.Thm_BalanceSpecification_languageEntropy_language_eq_entropy


set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
open Filter
open scoped Topology
variable {A : Type*} [Fintype A] [TopologicalSpace A] [DiscreteTopology A]
omit [DiscreteTopology A]
namespace BalanceSpecification
theorem _root_.solution {X : ShiftSpace A}
    (hX : X.carrier.Nonempty)
    (hless : ∀ (Y : ShiftSpace A) (hY : Y.carrier.Nonempty),
      Y.carrier ⊂ X.carrier → entropy Y hY < entropy X hX) : EntropyMinimal X := by
  intro Y hproper
  by_cases hY : Y.carrier.Nonempty
  · rw [languageEntropy_language_eq_entropy hY, languageEntropy_language_eq_entropy hX]
    exact_mod_cast hless Y hY hproper
  · have hYempty : Y.carrier = ∅ := Set.not_nonempty_iff_eq_empty.mp hY
    rw [languageEntropy_eq_bot_of_empty_carrier hYempty, languageEntropy_language_eq_entropy hX]
    exact EReal.bot_lt_coe _
end BalanceSpecification
