-- Prove2me | solution 1 for BSLambda.Construction.conflict_gateCoord
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T00:50:25.497698+00:00
-- url     : https://prove2.me/submissions/516d2e4b-cfb6-4b48-828a-fa4d1db169cf

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Basic
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Conflict
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.Construction
variable {ι : Type*} {r : ℕ}
variable [DecidableEq ι] {Arc : ι → ι → Bool} {γ : ι → ι → Fin r} {i j : ι}


theorem solution (hji : j ≠ i) (hij : Arc i j) :
    (cert Arc γ i).Conflict (cert Arc γ j) (gateCoord γ i j) := by
  exact ⟨false, by simp [cert,gateCoord,hji,hij], by simp [cert,gateCoord]⟩
