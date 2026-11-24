-- Prove2me | solution 2 for BSLambda.flipSet_apply_of_notMem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T00:47:54.211373+00:00
-- url     : https://prove2.me/submissions/7feb4575-aa14-44e3-8a7a-bc8b18d14d96

module
public import Mathlib.InformationTheory.Hamming
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
public import Theorems.Thm_BSLambda_zeroInput_apply
public import Theorems.Thm_BSLambda_flipSet_apply_of_mem
attribute [local simp] BSLambda.zeroInput_apply
attribute [local simp] BSLambda.flipSet_apply_of_mem

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
variable {V : Type*}
variable [DecidableEq V]
namespace BSLambda
theorem _root_.solution {x : Input V} {A : Finset V} {v : V} (hv : v ∉ A) :
    flipSet x A v = x v := by simp [flipSet, hv]
end BSLambda
