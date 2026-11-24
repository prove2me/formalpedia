-- Prove2me | solution 1 for BSLambda.le_bs_of_family
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T00:55:58.771413+00:00
-- url     : https://prove2.me/submissions/e37a0cb5-9fd7-42bb-8cea-5961da54faf4

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Sensitivity
public import Theorems.Thm_BSLambda_le_bsAt_of_family
public import Theorems.Thm_BSLambda_bsAt_le_bs

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BSLambda
theorem _root_.solution {f : Input V → Bool} {x : Input V} {𝓑 : Finset (Finset V)}
    (h : IsBlockFamily f x 𝓑) : 𝓑.card ≤ bs f :=
  (le_bsAt_of_family h).trans (bsAt_le_bs f x)
end BSLambda
