-- Prove2me | solution 1 for BSLambda.Final.lam_rpow_212_lt_bs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:41:31.380799+00:00
-- url     : https://prove2.me/submissions/408f0050-557e-4f05-86e2-dcf3144fc8ba

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_CertUnion
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Paley_Tournament
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Conflict
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_BlockSens
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_GateExists
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Multiplicative
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Main
public import Theorems.Thm_BSLambda_Final_bs_ge_real
public import Theorems.Thm_BSLambda_Final_lam_sq_le
public import Theorems.Thm_BSLambda_Final_U_lt
public import Theorems.Thm_BSLambda_Final_U_pos
public import Theorems.Thm_BSLambda_Final_rpow_1_06_lt
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
theorem _root_.solution (h₁ : ListOne γ) (h₂ : ListTwo γ) :
    lam (ind Arc γ) ^ (2.12 : ℝ) < (bs (ind Arc γ) : ℝ) := by
  calc lam (ind Arc γ) ^ (2.12 : ℝ)
      = (lam (ind Arc γ) ^ (2 : ℕ)) ^ (1.06 : ℝ) := rpow_eq_sq_rpow (lam_nonneg _) (by norm_num)
    _ ≤ U ^ (1.06 : ℝ) := Real.rpow_le_rpow (by positivity) (lam_sq_le h₁ h₂) (by norm_num)
    _ ≤ (7924 : ℝ) ^ (1.06 : ℝ) := Real.rpow_le_rpow U_pos.le U_lt.le (by norm_num)
    _ < 14011 := rpow_1_06_lt
    _ ≤ (bs (ind Arc γ) : ℝ) := bs_ge_real
end BSLambda.Final
