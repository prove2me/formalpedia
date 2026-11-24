-- Prove2me | solution 1 for BSLambda.PartialAssign.dist_le_codim
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:40:53.104735+00:00
-- url     : https://prove2.me/submissions/439bc4f4-0f73-4108-80b0-d34a8f27d24f

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Subcube
public import Theorems.Thm_BSLambda_PartialAssign_violSet_subset_fixedSet

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.PartialAssign
variable {V : Type*}
variable [Fintype V]
namespace BSLambda.PartialAssign
theorem _root_.solution (P : PartialAssign V) (x : Input V) : P.dist x ≤ P.codim :=
  Finset.card_le_card (P.violSet_subset_fixedSet x)
end BSLambda.PartialAssign
