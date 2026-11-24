-- Prove2me | solution 2 for BSLambda.PartialAssign.mem_fixedSet_iff_exists
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:02:17.35941+00:00
-- url     : https://prove2.me/submissions/f8e99b40-2356-46ea-a109-3cf9ae10a402

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Subcube
public import Theorems.Thm_BSLambda_PartialAssign_mem_fixedSet_iff_ne_none

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.PartialAssign
variable {V : Type*}
variable [Fintype V]
namespace BSLambda.PartialAssign
theorem _root_.solution {P : PartialAssign V} {v : V} :
    v ∈ P.fixedSet ↔ ∃ b, P v = some b := by
  rw [mem_fixedSet_iff_ne_none, Option.ne_none_iff_exists']
end BSLambda.PartialAssign
