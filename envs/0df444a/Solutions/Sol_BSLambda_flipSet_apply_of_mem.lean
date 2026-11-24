-- Prove2me | solution 1 for BSLambda.flipSet_apply_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T00:47:14.80715+00:00
-- url     : https://prove2.me/submissions/19bbc8f9-a9f1-458b-b2da-d9873f16ba09

module
public import Mathlib.InformationTheory.Hamming
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
public import Theorems.Thm_BSLambda_zeroInput_apply
attribute [local simp] BSLambda.zeroInput_apply

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
variable {V : Type*}
variable [DecidableEq V]
namespace BSLambda
theorem _root_.solution {x : Input V} {A : Finset V} {v : V} (hv : v ∈ A) :
    flipSet x A v = !x v := by simp [flipSet, hv]
end BSLambda
