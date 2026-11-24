-- Prove2me | solution 1 for BSLambda.PartialAssign.Conflict.mem_violSet
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T00:49:27.039745+00:00
-- url     : https://prove2.me/submissions/785f6523-f638-4b07-8849-6e327268bf1e

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Subcube
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.PartialAssign
variable {V : Type*}
variable [Fintype V]


theorem solution {P Q : PartialAssign V} {v : V} (h : P.Conflict Q v)
    {x : Input V} (hx : P.Sat x) : v ∈ Q.violSet x := by
  obtain ⟨b,hb,hb'⟩ := h
  have hv := hx v b hb
  cases b <;> simp [violSet,hb',hv]
