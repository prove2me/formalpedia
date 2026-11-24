-- Prove2me | solution 1 for BalanceSpecification.exists_specification_shift_entropy_log_nat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:57:27.945224+00:00
-- url     : https://prove2.me/submissions/2536db4f-322a-451b-a371-0a8d901936ea

module
public import Definitions.Def_BalanceSpecificaton_ProductShift
public import Definitions.Def_BalanceSpecificaton_EntropyRealization
public import Definitions.Def_BalanceSpecificaton_SGapEntropy
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_EntropyModel
public import Theorems.Thm_BalanceSpecification_entropy_constantShift
public import Theorems.Thm_BalanceSpecification_entropy_productShift
public import Theorems.Thm_BalanceSpecification_entropy_unrestrictedShift
public import Theorems.Thm_BalanceSpecification_hasSpecification_constantShift
public import Theorems.Thm_BalanceSpecification_hasSpecification_productShift
public import Theorems.Thm_BalanceSpecification_hasSpecification_unrestrictedShift


set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
namespace BalanceSpecification
theorem _root_.solution
    [TopologicalSpace Bool] [DiscreteTopology Bool] (n : ℕ) (hn : 1 ≤ n) :
    ∃ X : ShiftSpace (Fin n × Bool), ∃ hX : X.carrier.Nonempty,
      HasSpecification X ∧ entropy X hX = Real.log n := by
  let : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  let X := productShift (unrestrictedShift (Fin n)) (constantShift true)
  have hX : X.carrier.Nonempty :=
    productShift_nonempty unrestrictedShift_nonempty (constantShift_nonempty true)
  refine ⟨X, hX, hasSpecification_productShift hasSpecification_unrestrictedShift
    (hasSpecification_constantShift true), ?_⟩
  change entropy (productShift (unrestrictedShift (Fin n)) (constantShift true)) _ = Real.log n
  rw [entropy_productShift unrestrictedShift_nonempty (constantShift_nonempty true),
    entropy_unrestrictedShift, entropy_constantShift, Fintype.card_fin, add_zero]
end BalanceSpecification
