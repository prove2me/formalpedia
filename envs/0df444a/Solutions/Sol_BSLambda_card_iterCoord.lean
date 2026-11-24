-- Prove2me | solution 1 for BSLambda.card_iterCoord
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:34:56.996868+00:00
-- url     : https://prove2.me/submissions/cc0c940b-b7d2-4f72-a30a-f42699539506

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Sensitivity
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Composition

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open Function
universe u
namespace BSLambda
theorem _root_.solution (V : Type*) [Fintype V] :
    ∀ m, Fintype.card (IterCoord V m) = Fintype.card V ^ m
  | 0 => Fintype.card_punit
  | m + 1 => by
      change Fintype.card (V × IterCoord V m) = _
      rw [Fintype.card_prod, solution V m, pow_succ']
end BSLambda
