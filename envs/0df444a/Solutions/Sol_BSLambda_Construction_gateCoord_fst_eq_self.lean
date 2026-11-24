-- Prove2me | solution 1 for BSLambda.Construction.gateCoord_fst_eq_self
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T00:50:36.490559+00:00
-- url     : https://prove2.me/submissions/ebf2a777-e40e-4c06-babe-3b0d0ac69fc9

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


theorem solution {γ : ι → ι → Fin r} {i : ι} {v : Coord ι r} (h : v.2 = γ i v.1) :
    gateCoord γ i v.1 = v := by
  exact Prod.ext rfl h.symm
