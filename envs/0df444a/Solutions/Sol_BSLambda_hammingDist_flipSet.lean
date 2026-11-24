-- Prove2me | solution 1 for BSLambda.hammingDist_flipSet
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T00:48:29.356266+00:00
-- url     : https://prove2.me/submissions/c4c6a4f0-1f73-410f-b477-42f66d793e42

module
public import Mathlib.InformationTheory.Hamming
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
variable {V : Type*}
variable [Fintype V] [DecidableEq V]


theorem solution (x : Input V) (A : Finset V) :
    hammingDist x (flipSet x A) = A.card := by
  unfold hammingDist flipSet
  congr 1
  ext v
  by_cases hv : v ∈ A <;> cases h : x v <;> simp [hv,h]
