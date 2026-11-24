-- Prove2me | solution 1 for BSLambda.LLL.card_discSet_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:28:41.265196+00:00
-- url     : https://prove2.me/submissions/87acc27d-6ccb-4fbd-ab93-e933568fa36b

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Asymmetric
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Basic
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_Binomial
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Obstruction

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.LLL
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {r : ℕ}
omit [Fintype ι]
variable {Arc : ι → ι → Bool} {γ : ι → ι → Fin r} {Z : ι → Finset (Fin r)} {T : Finset ι}
  {p : ι × ι}
omit [DecidableEq ι]
namespace BSLambda.LLL
theorem _root_.solution (T : Finset ι) (h : ι) :
    (discSet γ Z T h).card = ∑ j ∈ T, if Z j ⊆ {γ h j} then 0 else 1 := by
  rw [discSet, Finset.card_filter]
  exact Finset.sum_congr rfl fun j _ ↦ ite_not _ _ _
end BSLambda.LLL
