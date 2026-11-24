-- Prove2me | solution 1 for BSLambda.Final.lam_iter_rpow_le_bs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:47:13.764969+00:00
-- url     : https://prove2.me/submissions/8f47bbd6-2c3a-49b6-9cdd-dfb6670f7a4c

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_CertUnion
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Paley_Tournament
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Conflict
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_BlockSens
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_GateExists
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Multiplicative
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Main
public import Theorems.Thm_BSLambda_Final_lam_rpow_le
public import Theorems.Thm_BSLambda_Final_bs_iter_ge
public import Theorems.Thm_BSLambda_lam_iterFun_eq
public import Theorems.Thm_BSLambda_lam_nonneg


set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.Final
open Construction
variable {γ : Idx → Idx → Fin r}
namespace BSLambda.Final
theorem _root_.solution (h₁ : ListOne γ) (h₂ : ListTwo γ) (m : ℕ) :
    lam (iterFun (ind Arc γ) m) ^ alpha ≤ (bs (iterFun (ind Arc γ) m) : ℝ) := by
  calc lam (iterFun (ind Arc γ) m) ^ alpha
      = (lam (ind Arc γ) ^ m) ^ alpha := by rw [lam_iterFun_eq (ind Arc γ) m]
    _ = (lam (ind Arc γ) ^ alpha) ^ m := by
        rw [← Real.rpow_natCast (lam (ind Arc γ)) m, ← Real.rpow_mul (lam_nonneg _), mul_comm,
          Real.rpow_mul (lam_nonneg _), Real.rpow_natCast]
    _ ≤ (14011 : ℝ) ^ m := by
        gcongr
        · exact Real.rpow_nonneg (lam_nonneg _) _
        · exact lam_rpow_le h₁ h₂
    _ ≤ (bs (iterFun (ind Arc γ) m) : ℝ) := by exact_mod_cast bs_iter_ge m
end BSLambda.Final
