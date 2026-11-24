-- Prove2me | solution 1 for BSLambda.blockFamilyCards_bddAbove
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T00:53:51.62309+00:00
-- url     : https://prove2.me/submissions/f11c3f81-c3f2-4bde-a7c1-061abe8798eb

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Sensitivity
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
variable {V : Type*} [Fintype V] [DecidableEq V]
omit [Fintype V]


theorem solution [Finite V] (f : Input V → Bool) (x : Input V) :
    BddAbove (blockFamilyCards f x) := by
  classical
  letI := Fintype.ofFinite V
  refine ⟨Fintype.card (Finset V),?_⟩
  rintro n ⟨F,hF,rfl⟩; exact Finset.card_le_univ F
