-- Prove2me | solution 1 for BSLambda.LLL.active_flag_typeA
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:27:56.208822+00:00
-- url     : https://prove2.me/submissions/0e813966-2073-4261-9505-d7d3d329242b

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Asymmetric
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Basic
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_Binomial
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Obstruction
public import Theorems.Thm_BSLambda_LLL_Flag1_nonOwners_of_top_eq_none
public import Theorems.Thm_BSLambda_LLL_Flag1_active_iff_of_top_eq_none

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.LLL
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {r : ℕ}
omit [Fintype ι]
namespace BSLambda.LLL
theorem _root_.solution {Arc : ι → ι → Bool} {S : Finset ι} (hS : S.card = 5) {h : ι}
    (hh : h ∈ S) (hdom : ∀ j ∈ S, j ≠ h → Arc h j = true) :
    ({ owner := h, top := none, bot := S.erase h } : Flag1 ι).Active Arc ∧
      ({ owner := h, top := none, bot := S.erase h } : Flag1 ι).supp = S := by
  refine ⟨(Flag1.active_iff_of_top_eq_none rfl).2 ⟨Finset.notMem_erase _ _, ?_, ?_⟩, ?_⟩
  · rw [Finset.card_erase_of_mem hh, hS]
  · intro j hj
    exact hdom j (Finset.mem_of_mem_erase hj) (Finset.ne_of_mem_erase hj)
  · rw [Flag1.supp, Flag1.nonOwners_of_top_eq_none rfl]
    exact Finset.insert_erase hh
end BSLambda.LLL
