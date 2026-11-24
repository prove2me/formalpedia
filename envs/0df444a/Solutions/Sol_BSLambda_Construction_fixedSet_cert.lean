-- Prove2me | solution 1 for BSLambda.Construction.fixedSet_cert
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:12:24.569145+00:00
-- url     : https://prove2.me/submissions/71a02430-82a6-409d-9ed4-099730f12cda

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Sensitivity
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Subcube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Tournament
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Basic
public import Theorems.Thm_BSLambda_Construction_mem_block
public import Theorems.Thm_BSLambda_Construction_card_block
public import Theorems.Thm_BSLambda_Construction_gateCoord_fst
public import Theorems.Thm_BSLambda_Construction_gateCoord_fst_eq_self
public import Theorems.Thm_BSLambda_Construction_cert_apply
public import Theorems.Thm_BSLambda_Construction_cert_apply_of_fst_eq
public import Theorems.Thm_BSLambda_Construction_cert_apply_gateCoord
public import Theorems.Thm_BSLambda_Construction_cert_apply_eq_none
public import Theorems.Thm_BSLambda_PartialAssign_dist_eq_zero_iff
public import Theorems.Thm_BSLambda_PartialAssign_indUnion_eq_false_iff
public import Theorems.Thm_BSLambda_PartialAssign_indUnion_eq_true_iff
public import Theorems.Thm_BSLambda_PartialAssign_mem_cube
public import Theorems.Thm_BSLambda_PartialAssign_mem_fixedSet
public import Theorems.Thm_BSLambda_PartialAssign_mem_fixedSet_iff_ne_none
public import Theorems.Thm_BSLambda_PartialAssign_mem_violSet
public import Theorems.Thm_BSLambda_PartialAssign_proj_apply
public import Theorems.Thm_BSLambda_PartialAssign_proj_sat
public import Theorems.Thm_BSLambda_flipSet_apply_eq_self_iff
public import Theorems.Thm_BSLambda_flipSet_apply_of_mem
public import Theorems.Thm_BSLambda_flipSet_apply_of_notMem
public import Theorems.Thm_BSLambda_flipSet_empty
public import Theorems.Thm_BSLambda_flipSet_flipSet
public import Theorems.Thm_BSLambda_flipSet_left_inj
public import Theorems.Thm_BSLambda_flipSet_zeroInput_apply
public import Theorems.Thm_BSLambda_hammingDist_flipSet
public import Theorems.Thm_BSLambda_mem_commonIn
public import Theorems.Thm_BSLambda_mem_commonOut
public import Theorems.Thm_BSLambda_mem_inNbrs
public import Theorems.Thm_BSLambda_mem_middles
public import Theorems.Thm_BSLambda_mem_outNbrs
public import Theorems.Thm_BSLambda_zeroInput_apply
attribute [local simp] BSLambda.PartialAssign.dist_eq_zero_iff
attribute [local simp] BSLambda.PartialAssign.indUnion_eq_false_iff
attribute [local simp] BSLambda.PartialAssign.indUnion_eq_true_iff
attribute [local simp] BSLambda.PartialAssign.mem_cube
attribute [local simp] BSLambda.PartialAssign.mem_fixedSet
attribute [local simp] BSLambda.PartialAssign.mem_violSet
attribute [local simp] BSLambda.PartialAssign.proj_apply
attribute [local simp] BSLambda.PartialAssign.proj_sat
attribute [local simp] BSLambda.flipSet_apply_eq_self_iff
attribute [local simp] BSLambda.flipSet_apply_of_mem
attribute [local simp] BSLambda.flipSet_apply_of_notMem
attribute [local simp] BSLambda.flipSet_empty
attribute [local simp] BSLambda.flipSet_flipSet
attribute [local simp] BSLambda.flipSet_left_inj
attribute [local simp] BSLambda.flipSet_zeroInput_apply
attribute [local simp] BSLambda.hammingDist_flipSet
attribute [local simp] BSLambda.mem_commonIn
attribute [local simp] BSLambda.mem_commonOut
attribute [local simp] BSLambda.mem_inNbrs
attribute [local simp] BSLambda.mem_middles
attribute [local simp] BSLambda.mem_outNbrs
attribute [local simp] BSLambda.zeroInput_apply


attribute [local simp] BSLambda.Construction.mem_block
attribute [local simp] BSLambda.Construction.card_block
attribute [local simp] BSLambda.Construction.gateCoord_fst

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.Construction
variable {ι : Type*} {r : ℕ}
variable [Fintype ι] [DecidableEq ι] {Arc : ι → ι → Bool} {γ : ι → ι → Fin r} {i : ι}
namespace BSLambda.Construction
theorem _root_.solution :
    (cert Arc γ i).fixedSet = block i ∪ (outNbrs Arc i).image (gateCoord γ i) := by
  ext v
  simp only [PartialAssign.mem_fixedSet_iff_ne_none, Finset.mem_union, mem_block,
    Finset.mem_image, mem_outNbrs]
  constructor
  · intro hv
    by_cases h₁ : v.1 = i
    · exact Or.inl h₁
    · by_cases h₂ : Arc i v.1 ∧ v.2 = γ i v.1
      · exact Or.inr ⟨v.1, h₂.1, gateCoord_fst_eq_self h₂.2⟩
      · exact absurd (cert_apply_eq_none h₁ h₂) hv
  · rintro (h | ⟨j, hj, rfl⟩)
    · simp [cert_apply_of_fst_eq h]
    · rcases eq_or_ne j i with rfl | hji
      · simp [cert_apply, gateCoord]
      · simp [cert_apply_gateCoord hji hj]
end BSLambda.Construction
