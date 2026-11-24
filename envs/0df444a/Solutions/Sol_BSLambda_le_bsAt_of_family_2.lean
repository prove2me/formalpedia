-- Prove2me | solution 2 for BSLambda.le_bsAt_of_family
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T00:55:34.565358+00:00
-- url     : https://prove2.me/submissions/4928040f-737d-4245-93e3-1b56ab005192

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Sensitivity
public import Theorems.Thm_BSLambda_blockFamilyCards_bddAbove

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
variable {V : Type*} [Fintype V] [DecidableEq V]
omit [Fintype V]
namespace BSLambda
theorem _root_.solution [Finite V] {f : Input V → Bool} {x : Input V} {𝓑 : Finset (Finset V)}
    (h : IsBlockFamily f x 𝓑) : 𝓑.card ≤ bsAt f x :=
  le_csSup (blockFamilyCards_bddAbove f x) ⟨𝓑, h, rfl⟩
end BSLambda
