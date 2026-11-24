-- Prove2me | solution 2 for BSLambda.ne_flipSet_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T00:51:43.222258+00:00
-- url     : https://prove2.me/submissions/dfdccb0b-ce11-461e-a6c2-a0cd1fd1637d

module
public import Mathlib.InformationTheory.Hamming
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
public import Theorems.Thm_BSLambda_flipSet_apply_ne_self_iff

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
variable {V : Type*}
variable [DecidableEq V]
namespace BSLambda
theorem _root_.solution {x : Input V} {A : Finset V} {v : V} (hv : v ∈ A) :
    x v ≠ flipSet x A v := (flipSet_apply_ne_self_iff.2 hv).symm
end BSLambda
