-- Prove2me | solution 2 for BSLambda.flipSet_left_inj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T00:55:17.822371+00:00
-- url     : https://prove2.me/submissions/79905141-a071-4267-bf10-42a18382e81f

module
public import Mathlib.InformationTheory.Hamming
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
public import Theorems.Thm_BSLambda_flipSet_left_injective

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
variable {V : Type*}
variable [DecidableEq V]
namespace BSLambda
theorem _root_.solution {x y : Input V} {A : Finset V} :
    flipSet x A = flipSet y A ↔ x = y :=
  (flipSet_left_injective A).eq_iff
end BSLambda
