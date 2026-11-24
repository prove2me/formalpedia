-- Prove2me | solution 1 for BSLambda.hammingDist_flipSet_singleton
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T00:52:13.668484+00:00
-- url     : https://prove2.me/submissions/e704a76f-9c30-4383-ad37-3cf4a653f7d0

module
public import Mathlib.InformationTheory.Hamming
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
variable {V : Type*}
variable [Fintype V] [DecidableEq V]


theorem solution (x : Input V) (v : V) : hammingDist x (flipSet x {v}) = 1 := by
  classical
  unfold hammingDist
  have eq : (Finset.univ.filter fun j => x j ≠ flipSet x {v} j) = {v} := by
    ext j
    by_cases hj : j = v <;> cases h : x j <;> simp_all [flipSet]
  simp [eq]
