-- Prove2me | solution 1 for BSLambda.PartialAssign.conflict_of_mem_fixedSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:04:08.36081+00:00
-- url     : https://prove2.me/submissions/5051ea9e-7b1b-4460-b5b6-71f5ab203862

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
theorem _root_.solution {P Q : PartialAssign V} {x y : Input V} (hx : P.Sat x)
    (hy : Q.Sat y) {v : V} (hP : v ∈ P.fixedSet) (hQ : v ∈ Q.fixedSet) (hne : x v ≠ y v) :
    P.Conflict Q v := by
  obtain ⟨b, hb⟩ := mem_fixedSet_iff_exists.1 hP
  obtain ⟨b', hb'⟩ := mem_fixedSet_iff_exists.1 hQ
  rw [hx.eq_of_fixed hb, hy.eq_of_fixed hb'] at hne
  refine ⟨b, hb, ?_⟩
  rw [hb', Bool.eq_not_of_ne hne.symm]
end BSLambda.PartialAssign
