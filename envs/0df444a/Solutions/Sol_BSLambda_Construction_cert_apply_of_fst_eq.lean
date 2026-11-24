-- Prove2me | solution 1 for BSLambda.Construction.cert_apply_of_fst_eq
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T00:50:27.638069+00:00
-- url     : https://prove2.me/submissions/27a5723a-4b3d-411a-b850-050a406deea5

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
variable [DecidableEq ι]
variable {Arc : ι → ι → Bool} {γ : ι → ι → Fin r} {i j : ι} {v : Coord ι r} {b : Bool}


theorem solution (h : v.1 = i) : cert Arc γ i v = some true := by
  simp [cert,h]
