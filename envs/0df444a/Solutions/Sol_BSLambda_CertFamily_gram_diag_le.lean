-- Prove2me | solution 1 for BSLambda.CertFamily.gram_diag_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:23:01.889434+00:00
-- url     : https://prove2.me/submissions/4d661a17-f74c-407c-a4c5-8bdd12b0ffce

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Subcube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Bipartite
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_CertFamily
public import Theorems.Thm_BSLambda_CertFamily_owner_sat
public import Theorems.Thm_BSLambda_CertFamily_sensAt_le_c
public import Theorems.Thm_BSLambda_gram_diag


set_option autoImplicit true
@[expose] public section
public section
open BSLambda
variable {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]
open BSLambda.CertFamily
variable (F : CertFamily V ι)
namespace BSLambda.CertFamily
theorem _root_.solution (x : Ones F.ind) : gram F.ind x x ≤ (F.c : ℝ) := by
  rw [gram_diag]
  exact_mod_cast F.sensAt_le_c (F.owner_sat x)
end BSLambda.CertFamily
