-- Prove2me | solution 1 for BSLambda.PartialAssign.Conflict.ne
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T00:49:24.808882+00:00
-- url     : https://prove2.me/submissions/c0b5b98d-b376-4d90-a077-ec2f5baab0d4

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Subcube
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.PartialAssign
variable {V : Type*}


theorem solution {P Q : PartialAssign V} {v : V} (h : P.Conflict Q v)
    {x y : Input V} (hx : P.Sat x) (hy : Q.Sat y) : x v ≠ y v := by
  obtain ⟨b,hb,hb'⟩ := h
  rw [hx v b hb, hy v (!b) hb']; cases b <;> decide
