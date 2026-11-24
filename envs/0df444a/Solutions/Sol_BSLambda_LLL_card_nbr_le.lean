-- Prove2me | solution 1 for BSLambda.LLL.card_nbr_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:39:50.828172+00:00
-- url     : https://prove2.me/submissions/416d5797-e585-40b8-bed9-ffdb8e038ea6

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Obstruction
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_LLLBounds
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_GateExists
public import Theorems.Thm_BSLambda_LLL_card_nbr_one_one_le_D11
public import Theorems.Thm_BSLambda_LLL_card_nbr_one_two_le_D12
public import Theorems.Thm_BSLambda_LLL_card_nbr_two_one_le_D21
public import Theorems.Thm_BSLambda_LLL_card_nbr_two_two_le_D22

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.LLL
open Numerics Construction
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {r : ℕ} {Arc : ι → ι → Bool}
namespace BSLambda.LLL
theorem _root_.solution (hk : Fintype.card ι = 14011) (hT : IsDRTournamentWith Arc 7005 3502)
    (i : BadIdx Arc) (t : Bool) :
    ((nbr (badSupp (Arc := Arc)) i).filter fun j => badTy j = t).card
      ≤ badD (badTy i) t := by
  cases i with
  | inl F =>
    cases t with
    | false => exact card_nbr_one_one_le_D11 hT F
    | true => exact card_nbr_one_two_le_D12 hk F
  | inr S =>
    cases t with
    | false => exact card_nbr_two_one_le_D21 hT S
    | true => exact card_nbr_two_two_le_D22 hk S
end BSLambda.LLL
