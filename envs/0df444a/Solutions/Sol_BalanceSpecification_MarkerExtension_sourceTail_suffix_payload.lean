-- Prove2me | solution 1 for BalanceSpecification.MarkerExtension.sourceTail_suffix_payload
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:24:40.769038+00:00
-- url     : https://prove2.me/submissions/255af6c9-5193-4a71-8224-9b4a6efedb5a

module
public import Definitions.Def_BalanceSpecificaton_MarkerExtension
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_MarkerSuffix

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification BalanceSpecification.MarkerExtension
variable {A : Type*} [TopologicalSpace A] {Y : ShiftSpace A}
variable (M : ℕ)
  (hM : ∀ u ∈ language Y, ∀ v ∈ language Y,
    ∃ b ∈ language Y, b.length = M ∧ u ++ b ++ v ∈ language Y)
  (x : Y.carrier) (s : ℕ → ℕ)
namespace BalanceSpecification.MarkerExtension
theorem _root_.solution (u : PositiveLanguage Y) :
    sourceTail x (suffixLength M s u.val.length) <:+ sourcePayload M hM x s u :=
  ⟨u.val ++ sourceBridge M hM x s u, rfl⟩
end BalanceSpecification.MarkerExtension
