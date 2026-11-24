-- Prove2me | solution 1 for BSLambda.Final.lam_rpow_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:42:39.539268+00:00
-- url     : https://prove2.me/submissions/2c7fbaa5-e9e1-4cd6-b66a-79ef3da72874

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_CertUnion
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Paley_Tournament
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Conflict
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_BlockSens
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_GateExists
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Multiplicative
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Main
public import Theorems.Thm_BSLambda_Final_lam_sq_le
public import Theorems.Thm_BSLambda_Final_two_lt_alpha
public import Theorems.Thm_BSLambda_Final_U_rpow_alpha
public import Theorems.Thm_BSLambda_CertFamily_lam_sq_le
public import Theorems.Thm_BSLambda_lam_nonneg

section
@[expose] public section
namespace BSLambda
namespace Final
open Construction
variable {γ : Idx → Idx → Fin r}
private theorem rpow_eq_sq_rpow {x t s : ℝ} (hx : 0 ≤ x) (hts : t = 2 * s) :
    x ^ t = (x ^ (2 : ℕ)) ^ s := by
  subst hts
  rw [← Real.rpow_natCast x 2, ← Real.rpow_mul hx]
  norm_num
end Final
end BSLambda
end
end

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.Final
open Construction
variable {γ : Idx → Idx → Fin r}
namespace BSLambda.Final
theorem _root_.solution (h₁ : ListOne γ) (h₂ : ListTwo γ) : lam (ind Arc γ) ^ alpha ≤ 14011 := by
  calc lam (ind Arc γ) ^ alpha
      = (lam (ind Arc γ) ^ (2 : ℕ)) ^ (alpha / 2) := rpow_eq_sq_rpow (lam_nonneg _) (by ring)
    _ ≤ U ^ (alpha / 2) :=
        Real.rpow_le_rpow (sq_nonneg _) (lam_sq_le h₁ h₂) (by linarith [two_lt_alpha])
    _ = 14011 := U_rpow_alpha
end BSLambda.Final
