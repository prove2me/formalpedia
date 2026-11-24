-- Prove2me | solution 2 for BSLambda.Construction.cert_apply_gateCoord
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:06:07.042892+00:00
-- url     : https://prove2.me/submissions/2b740bb0-742e-4333-a667-20109b5b1774

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Sensitivity
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Subcube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Tournament
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Basic
public import Theorems.Thm_BSLambda_Construction_cert_eq_some_iff

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.Construction
variable {ι : Type*} {r : ℕ}
variable [DecidableEq ι]
variable {Arc : ι → ι → Bool} {γ : ι → ι → Fin r} {i j : ι} {v : Coord ι r} {b : Bool}
namespace BSLambda.Construction
theorem _root_.solution (hji : j ≠ i) (hij : Arc i j) :
    cert Arc γ i (gateCoord γ i j) = some false :=
  cert_eq_some_iff.2 (Or.inr ⟨hji, hij, rfl, rfl⟩)
end BSLambda.Construction
