-- Prove2me | solution 1 for BSLambda.nbrs_eq_image
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:10:09.968578+00:00
-- url     : https://prove2.me/submissions/0c35d810-71b1-40e9-a8d3-631bf731b462

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Sensitivity
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Hermitian
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Spectral
public import Theorems.Thm_BSLambda_mem_nbrs
public import Theorems.Thm_BSLambda_exists_eq_flipSet_singleton_of_hammingDist_eq_one
public import Theorems.Thm_BSLambda_flipSet_apply_eq_self_iff
public import Theorems.Thm_BSLambda_flipSet_apply_of_mem
public import Theorems.Thm_BSLambda_flipSet_apply_of_notMem
public import Theorems.Thm_BSLambda_flipSet_empty
public import Theorems.Thm_BSLambda_flipSet_flipSet
public import Theorems.Thm_BSLambda_flipSet_left_inj
public import Theorems.Thm_BSLambda_flipSet_zeroInput_apply
public import Theorems.Thm_BSLambda_hammingDist_flipSet
public import Theorems.Thm_BSLambda_hammingDist_flipSet_singleton
public import Theorems.Thm_BSLambda_mem_sensCoords
public import Theorems.Thm_BSLambda_zeroInput_apply
attribute [local simp] BSLambda.flipSet_apply_eq_self_iff
attribute [local simp] BSLambda.flipSet_apply_of_mem
attribute [local simp] BSLambda.flipSet_apply_of_notMem
attribute [local simp] BSLambda.flipSet_empty
attribute [local simp] BSLambda.flipSet_flipSet
attribute [local simp] BSLambda.flipSet_left_inj
attribute [local simp] BSLambda.flipSet_zeroInput_apply
attribute [local simp] BSLambda.hammingDist_flipSet
attribute [local simp] BSLambda.zeroInput_apply



set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open scoped Matrix Matrix.Norms.L2Operator
variable {V : Type*} [Fintype V]
variable [DecidableEq V]
namespace BSLambda
theorem _root_.solution (f : Input V → Bool) (x : Input V) :
    nbrs f x = (sensCoords f x).image fun v => flipSet x {v} := by
  ext y
  simp only [mem_nbrs, Finset.mem_image, mem_sensCoords, SensitiveCoord]
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨v, rfl⟩ := exists_eq_flipSet_singleton_of_hammingDist_eq_one h1
    exact ⟨v, h2.symm, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨hammingDist_flipSet_singleton x v, hv.symm⟩
end BSLambda
