-- Prove2me | solution 1 for BalanceSpecification.exists_specification_shift_of_entropy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:44:26.311193+00:00
-- url     : https://prove2.me/submissions/a7c1c786-c8f8-4bdd-9787-3e9f6ecee26d

module
public import Definitions.Def_BalanceSpecificaton_ProductShift
public import Definitions.Def_BalanceSpecificaton_EntropyRealization
public import Definitions.Def_BalanceSpecificaton_SGapEntropy
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_EntropyModel
public import Theorems.Thm_BalanceSpecification_exists_log_card_entropy_decomposition
public import Theorems.Thm_BalanceSpecification_exists_binary_specification_shift_of_entropy_lt_log_two
public import Theorems.Thm_BalanceSpecification_entropy_productShift
public import Theorems.Thm_BalanceSpecification_entropy_unrestrictedShift
public import Theorems.Thm_BalanceSpecification_hasSpecification_productShift
public import Theorems.Thm_BalanceSpecification_hasSpecification_unrestrictedShift


set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
namespace BalanceSpecification
theorem _root_.solution
    [TopologicalSpace Bool] [DiscreteTopology Bool]
    {h : ℝ} (hh : 0 ≤ h) :
    ∃ n : ℕ, 1 ≤ n ∧ ∃ X : ShiftSpace (Fin n × Bool), ∃ hX : X.carrier.Nonempty,
      HasSpecification X ∧ entropy X hX = h := by
  obtain ⟨n, hn, hres, hsmall⟩ := exists_log_card_entropy_decomposition hh
  let : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  obtain ⟨Y, hY, hspec, hentropy⟩ :=
    exists_binary_specification_shift_of_entropy_lt_log_two hres hsmall
  let X := productShift (unrestrictedShift (Fin n)) Y
  have hX : X.carrier.Nonempty := productShift_nonempty unrestrictedShift_nonempty hY
  refine ⟨n, hn, X, hX, hasSpecification_productShift hasSpecification_unrestrictedShift hspec, ?_⟩
  change entropy (productShift (unrestrictedShift (Fin n)) Y) _ = h
  rw [entropy_productShift unrestrictedShift_nonempty hY, entropy_unrestrictedShift,
    Fintype.card_fin, hentropy]
  ring
end BalanceSpecification
