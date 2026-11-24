-- Prove2me | solution 1 for BSLambda.LLL.card_arcSet_erase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:26:43.184866+00:00
-- url     : https://prove2.me/submissions/b939be3e-e621-482a-93e8-3c7518dc59e3

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Asymmetric
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Basic
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_Binomial
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Obstruction
public import Theorems.Thm_BSLambda_LLL_card_arcSet

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.LLL
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {r : ℕ}
omit [Fintype ι]
namespace BSLambda.LLL
theorem _root_.solution {Arc : ι → ι → Bool} (hT : IsTournament Arc)
    {S : Finset ι} (hS : S.card = 9) {h : ι}
    (hh : h ∈ S) : (arcSet Arc (S.erase h)).card = 28 := by
  rw [card_arcSet hT, Finset.card_erase_of_mem hh, hS]
  rfl
end BSLambda.LLL
