-- Prove2me | solution 1 for BSLambda.Construction.block_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T00:52:25.726021+00:00
-- url     : https://prove2.me/submissions/ac153fec-e261-4eac-8fab-4aadac6f6e49

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Sensitivity
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Subcube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Tournament
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Basic
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.Construction
variable {ι : Type*} {r : ℕ}


theorem solution {i j : ι} (h : i ≠ j) :
    Disjoint (block i : Finset (Coord ι r)) (block j) := by
  apply Finset.disjoint_left.mpr
  rintro ⟨a,b⟩ h₁ h₂
  simp [block] at h₁ h₂
  exact h (by grind)
