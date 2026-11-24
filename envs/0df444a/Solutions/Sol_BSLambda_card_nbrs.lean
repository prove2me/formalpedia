-- Prove2me | solution 1 for BSLambda.card_nbrs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:11:08.808791+00:00
-- url     : https://prove2.me/submissions/069b031b-d34e-41b2-9e2d-65954533f517

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Sensitivity
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Hermitian
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Spectral
public import Theorems.Thm_BSLambda_nbrs_eq_image
public import Theorems.Thm_BSLambda_flipSet_singleton_injective


set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open scoped Matrix Matrix.Norms.L2Operator
variable {V : Type*} [Fintype V]
variable [DecidableEq V]
namespace BSLambda
theorem _root_.solution (f : Input V → Bool) (x : Input V) : (nbrs f x).card = sensAt f x := by
  rw [nbrs_eq_image, Finset.card_image_of_injective _ (flipSet_singleton_injective x), sensAt]
end BSLambda
