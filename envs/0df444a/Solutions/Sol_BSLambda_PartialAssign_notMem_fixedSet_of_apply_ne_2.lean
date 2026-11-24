-- Prove2me | solution 2 for BSLambda.PartialAssign.notMem_fixedSet_of_apply_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:04:03.802998+00:00
-- url     : https://prove2.me/submissions/3eacb863-8fa6-4800-b85b-f2615c755c93

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Subcube
public import Theorems.Thm_BSLambda_PartialAssign_Sat_eq_of_fixed
public import Theorems.Thm_BSLambda_PartialAssign_Conflict_symm
public import Theorems.Thm_BSLambda_PartialAssign_mem_fixedSet_iff_exists

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.PartialAssign
variable {V : Type*}
variable [Fintype V]
namespace BSLambda.PartialAssign
theorem _root_.solution {P : PartialAssign V} {x y : Input V} (hx : P.Sat x)
    (hy : P.Sat y) {v : V} (hne : x v ≠ y v) : v ∉ P.fixedSet := fun hv ↦ by
  obtain ⟨b, hb⟩ := mem_fixedSet_iff_exists.1 hv
  exact hne ((hx.eq_of_fixed hb).trans (hy.eq_of_fixed hb).symm)
end BSLambda.PartialAssign
