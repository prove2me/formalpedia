-- Prove2me | solution 1 for BSLambda.LLL.active_flag_typeB
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:28:05.520804+00:00
-- url     : https://prove2.me/submissions/a33f4f70-d611-4d67-a779-84c4687ce42b

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Asymmetric
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Basic
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_Binomial
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Obstruction
public import Theorems.Thm_BSLambda_LLL_Flag1_nonOwners_of_top_eq_some
public import Theorems.Thm_BSLambda_LLL_Flag1_active_iff_of_top_eq_some
public import Theorems.Thm_BSLambda_PartialAssign_Conflict_symm


set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.LLL
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {r : ℕ}
omit [Fintype ι]
namespace BSLambda.LLL
theorem _root_.solution {Arc : ι → ι → Bool} {S : Finset ι} (hS : S.card = 5) {h a : ι}
    (hh : h ∈ S) (ha : a ∈ S) (hah : a ≠ h) (harc : Arc a h = true)
    (hdom : ∀ j ∈ S, j ≠ h → j ≠ a → Arc h j = true ∧ Arc a j = true) :
    ({ owner := h, top := some a, bot := (S.erase h).erase a } : Flag1 ι).Active Arc ∧
      ({ owner := h, top := some a, bot := (S.erase h).erase a } : Flag1 ι).supp = S := by
  have haE : a ∈ S.erase h := Finset.mem_erase.mpr ⟨hah, ha⟩
  refine ⟨(Flag1.active_iff_of_top_eq_some rfl).2
      ⟨Ne.symm hah, fun hc ↦ Finset.notMem_erase h S (Finset.mem_of_mem_erase hc),
        Finset.notMem_erase _ _, ?_, harc, ?_⟩, ?_⟩
  · rw [Finset.card_erase_of_mem haE, Finset.card_erase_of_mem hh, hS]
  · intro j hj
    have hj' := Finset.mem_of_mem_erase hj
    exact hdom j (Finset.mem_of_mem_erase hj') (Finset.ne_of_mem_erase hj')
      (Finset.ne_of_mem_erase hj)
  · rw [Flag1.supp, Flag1.nonOwners_of_top_eq_some rfl, Finset.insert_erase haE,
      Finset.insert_erase hh]
end BSLambda.LLL
