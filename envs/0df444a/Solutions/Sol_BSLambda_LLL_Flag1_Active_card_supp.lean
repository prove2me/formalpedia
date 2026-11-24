-- Prove2me | solution 1 for BSLambda.LLL.Flag1.Active.card_supp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:27:35.93882+00:00
-- url     : https://prove2.me/submissions/3ba64030-4dce-4a12-a849-50de97fded04

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Asymmetric
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Basic
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_Binomial
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Obstruction
public import Theorems.Thm_BSLambda_LLL_Flag1_Active_owner_notMem_nonOwners
public import Theorems.Thm_BSLambda_LLL_Flag1_Active_card_nonOwners

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.LLL
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {r : ℕ}
open BSLambda.LLL.Flag1
omit [Fintype ι]
variable {F : Flag1 ι} {Arc : ι → ι → Bool} {a j : ι} {p : ι × ι}
open BSLambda.LLL.Flag1.Active
variable (hF : F.Active Arc)
include hF
namespace BSLambda.LLL.Flag1.Active
theorem _root_.solution : F.supp.card = 5 := by
  rw [supp, Finset.card_insert_of_notMem hF.owner_notMem_nonOwners, hF.card_nonOwners]
end BSLambda.LLL.Flag1.Active
