-- Prove2me | solution 1 for BSLambda.Construction.arc_and_snd_eq_of_cert_eq_some
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:11:59.6528+00:00
-- url     : https://prove2.me/submissions/bb73899d-3fe3-473e-83e8-eed4aad6b289

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
theorem _root_.solution (h : v.1 ≠ i) (hb : cert Arc γ i v = some b) :
    Arc i v.1 ∧ v.2 = γ i v.1 := by
  obtain ⟨-, ha, hg, -⟩ := (cert_eq_some_iff.1 hb).resolve_left fun hc ↦ h hc.1
  exact ⟨ha, hg⟩
end BSLambda.Construction
