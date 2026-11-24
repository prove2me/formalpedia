-- Prove2me | solution 1 for BSLambda.Final.bs_div_lam_sq_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:47:12.803015+00:00
-- url     : https://prove2.me/submissions/166c7166-3e2b-4ca2-a99c-1575b769192c

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_CertUnion
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Paley_Tournament
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Conflict
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_BlockSens
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_GateExists
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Multiplicative
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Main
public import Theorems.Thm_BSLambda_Final_lam_sq_le
public import Theorems.Thm_BSLambda_Final_U_pos
public import Theorems.Thm_BSLambda_Final_bs_iter_ge
public import Theorems.Thm_BSLambda_CertFamily_lam_sq_le
public import Theorems.Thm_BSLambda_lam_iterFun_eq


set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.Final
open Construction
variable {γ : Idx → Idx → Fin r}
namespace BSLambda.Final
theorem _root_.solution (h₁ : ListOne γ) (h₂ : ListTwo γ) (m : ℕ) :
    (14011 / U) ^ m * lam (iterFun (ind Arc γ) m) ^ 2
      ≤ (bs (iterFun (ind Arc γ) m) : ℝ) := by
  have hlam_sq : lam (iterFun (ind Arc γ) m) ^ 2 ≤ U ^ m := by
    rw [lam_iterFun_eq (ind Arc γ) m]
    calc (lam (ind Arc γ) ^ m) ^ 2 = (lam (ind Arc γ) ^ 2) ^ m := by ring
      _ ≤ U ^ m := pow_le_pow_left₀ (sq_nonneg _) (lam_sq_le h₁ h₂) m
  have hU : (0 : ℝ) < U := U_pos
  calc (14011 / U) ^ m * lam (iterFun (ind Arc γ) m) ^ 2
      ≤ (14011 / U) ^ m * U ^ m := mul_le_mul_of_nonneg_left hlam_sq (by positivity)
    _ = 14011 ^ m := by rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero m U_pos.ne')]
    _ ≤ bs (iterFun (ind Arc γ) m) := by exact_mod_cast bs_iter_ge m
end BSLambda.Final
