-- Prove2me | solution 1 for BSLambda.PartialAssign.codim_eq_card_fixedSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T00:49:40.501404+00:00
-- url     : https://prove2.me/submissions/9924634c-e237-4ea3-8020-44445ae891b3

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Subcube

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.PartialAssign
variable {V : Type*}
variable [Fintype V]
namespace BSLambda.PartialAssign
theorem _root_.solution (P : PartialAssign V) : P.codim = P.fixedSet.card := rfl
end BSLambda.PartialAssign
