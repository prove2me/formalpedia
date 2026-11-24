-- Prove2me | solution 1 for BSLambda.flipSet_filter_ne
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T00:54:00.95382+00:00
-- url     : https://prove2.me/submissions/b01754ce-8b92-4485-bce6-256519176bb7

module
public import Mathlib.InformationTheory.Hamming
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
variable {V : Type*}
variable [Fintype V] [DecidableEq V]


theorem solution (x y : Input V) :
    flipSet x (Finset.univ.filter fun v ↦ x v ≠ y v) = y := by
  funext v; cases h : x v <;> cases k : y v <;> simp [flipSet,h,k]
