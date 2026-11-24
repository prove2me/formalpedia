-- Prove2me | solution 2 for BSLambda.PartialAssign.Sat.flipSet_singleton
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:09:37.30827+00:00
-- url     : https://prove2.me/submissions/4fde9d33-5a5e-4c9c-b1d6-de0b7e6eaf3d

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Subcube
public import Theorems.Thm_BSLambda_PartialAssign_Sat_eq_of_fixed
public import Theorems.Thm_BSLambda_PartialAssign_mem_fixedSet_iff_exists
public import Theorems.Thm_BSLambda_flipSet_apply_of_notMem
attribute [local simp] BSLambda.flipSet_apply_of_notMem



set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.PartialAssign
variable {V : Type*}
variable [Fintype V] [DecidableEq V]
namespace BSLambda.PartialAssign
namespace Sat
theorem _root_.solution {P : PartialAssign V} {x : Input V} (hx : P.Sat x) {v : V}
    (hv : v ∉ P.fixedSet) : P.Sat (flipSet x {v}) := fun w b hw ↦ by
  have hwv : w ≠ v := fun h ↦ hv (h ▸ mem_fixedSet_iff_exists.2 ⟨b, hw⟩)
  rw [flipSet_apply_of_notMem (Finset.notMem_singleton.2 hwv)]
  exact hx.eq_of_fixed hw
end Sat
end BSLambda.PartialAssign
