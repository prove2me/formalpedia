-- Prove2me | solution 1 for BSLambda.LLL.Flag1.Active.card_arcs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:27:36.645797+00:00
-- url     : https://prove2.me/submissions/6a7879b9-77eb-44b1-ad53-6ff173e2b814

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Asymmetric
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Basic
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_Binomial
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Obstruction
public import Theorems.Thm_BSLambda_LLL_card_arcSet
public import Theorems.Thm_BSLambda_LLL_Flag1_Active_card_nonOwners

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.LLL
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {r : ℕ}
omit [Fintype ι]
namespace BSLambda.LLL
namespace Flag1.Active
theorem _root_.solution {F : Flag1 ι} {Arc : ι → ι → Bool} (hT : IsTournament Arc)
    (hF : F.Active Arc) : (arcSet Arc F.nonOwners).card = 6 := by
  rw [card_arcSet hT, hF.card_nonOwners]
  rfl
end Flag1.Active
end BSLambda.LLL
