-- Prove2me | solution 1 for BSLambda.apply_ne_of_adj_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:04:29.827051+00:00
-- url     : https://prove2.me/submissions/f825c35d-d079-4bfa-88f6-60e014e9137d

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Sensitivity
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Hermitian
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Spectral
public import Theorems.Thm_BSLambda_adj_eq_zero_of_apply_eq

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open scoped Matrix Matrix.Norms.L2Operator
variable {V : Type*} [Fintype V]
namespace BSLambda
theorem _root_.solution (f : Input V → Bool) {x y : Input V} (h : adj f x y ≠ 0) :
    f x ≠ f y :=
  fun hf ↦ h (adj_eq_zero_of_apply_eq f hf)
end BSLambda
