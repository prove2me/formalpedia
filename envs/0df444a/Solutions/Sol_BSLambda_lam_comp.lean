-- Prove2me | solution 1 for BSLambda.lam_comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:45:02.000322+00:00
-- url     : https://prove2.me/submissions/8246d04b-751f-4163-ae07-4b722eeb5e47

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_OpNorm
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Composition
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Multiplicative
public import Theorems.Thm_BSLambda_lam_comp_le
public import Theorems.Thm_BSLambda_le_lam_comp

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open scoped Matrix
variable {W V : Type*} [Fintype W] [DecidableEq W] [Fintype V] [DecidableEq V]
namespace BSLambda
theorem _root_.solution (f : Input W → Bool) (g : Input V → Bool) :
    lam (comp f g) = lam f * lam g :=
  le_antisymm (lam_comp_le f g) (le_lam_comp f g)
end BSLambda
