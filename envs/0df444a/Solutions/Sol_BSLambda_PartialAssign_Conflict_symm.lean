-- Prove2me | solution 1 for BSLambda.PartialAssign.Conflict.symm
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T00:48:20.780491+00:00
-- url     : https://prove2.me/submissions/c15664c5-a953-4bd8-9af7-78ae173f4713

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Subcube
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.PartialAssign
variable {V : Type*}


theorem solution {P Q : PartialAssign V} {v : V} (h : P.Conflict Q v) : Q.Conflict P v := by
  obtain ⟨b,hb,hc⟩ := h
  exact ⟨!b,hc,by simpa using hb⟩
