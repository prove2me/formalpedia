-- Prove2me | solution 1 for BSLambda.mem_sensCoords
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T00:51:36.030546+00:00
-- url     : https://prove2.me/submissions/75ab22d0-4ea4-407c-bd12-aba1d2ed942d

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Sensitivity

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BSLambda
theorem _root_.solution {f : Input V → Bool} {x : Input V} {v : V} :
    v ∈ sensCoords f x ↔ SensitiveCoord f x v := Finset.mem_filter_univ v
end BSLambda
