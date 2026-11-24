-- Prove2me | solution 1 for BSLambda.CertFamily.exists_flip_proj_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:22:52.621183+00:00
-- url     : https://prove2.me/submissions/9783e747-f336-4f9d-81bb-828a3d0e3dc8

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_CertFamily
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_GramClass
public import Theorems.Thm_BSLambda_CertFamily_conflict_conflictCoord
public import Theorems.Thm_BSLambda_PartialAssign_Conflict_mem_violSet
public import Theorems.Thm_BSLambda_PartialAssign_eq_flipSet_proj_of_dist_eq_one
public import Theorems.Thm_BSLambda_PartialAssign_mem_fixedSet_iff_exists
public import Theorems.Thm_BSLambda_PartialAssign_mem_violSet
attribute [local simp] BSLambda.PartialAssign.mem_violSet



set_option autoImplicit true
@[expose] public section
public section
open BSLambda
variable {V : Type*} [Fintype V] [DecidableEq V]
open BSLambda.CertFamily
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (F : CertFamily V ι)
namespace BSLambda.CertFamily
theorem _root_.solution {i j : ι} (hij : i ≠ j) {x : Input V} (hx : (F.P i).Sat x)
    (hd : (F.P j).dist x = 1) :
    ∃ p₀ ∈ (F.P i).fixedSet, x = flipSet ((F.P j).proj x) {p₀} := by
  obtain ⟨v, hviol, hx_eq⟩ := PartialAssign.eq_flipSet_proj_of_dist_eq_one hd
  obtain ⟨b, hb, -⟩ := F.conflict_conflictCoord hij
  -- The violation set is the singleton `{v}` and the conflict coordinate of `C_i` and
  -- `C_j` lies in it, so `v` is that conflict coordinate — in particular `C_i` fixes it.
  have hcv : F.conflictCoord hij = v := by
    have hmem := (F.conflict_conflictCoord hij).mem_violSet hx
    rwa [hviol, Finset.mem_singleton] at hmem
  exact ⟨v, PartialAssign.mem_fixedSet_iff_exists.2 ⟨b, hcv ▸ hb⟩, hx_eq⟩
end BSLambda.CertFamily
