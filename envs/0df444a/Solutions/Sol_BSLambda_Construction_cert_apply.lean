-- Prove2me | solution 1 for BSLambda.Construction.cert_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T00:48:29.981051+00:00
-- url     : https://prove2.me/submissions/2dd70727-3686-4f21-b48c-a60ac987fb6c

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
namespace BSLambda.Construction
theorem _root_.solution :
    cert Arc γ i v = if v.1 = i then some true
      else if Arc i v.1 ∧ v.2 = γ i v.1 then some false else none := rfl
end BSLambda.Construction
