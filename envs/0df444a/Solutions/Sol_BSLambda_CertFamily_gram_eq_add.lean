-- Prove2me | solution 1 for BSLambda.CertFamily.gram_eq_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:27:03.741169+00:00
-- url     : https://prove2.me/submissions/1402531a-0759-4005-8c32-9ac24baac1ed

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_GramClass
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_CertUnion
public import Theorems.Thm_BSLambda_CertFamily_diagMat_apply
public import Theorems.Thm_BSLambda_CertFamily_offMat_apply
public import Theorems.Thm_BSLambda_CertFamily_offMat_diag
public import Theorems.Thm_BSLambda_CertFamily_dist_eq_one_or_dist_eq_one
public import Theorems.Thm_BSLambda_CertFamily_dist_eq_two_of_dist_eq_one
public import Theorems.Thm_BSLambda_CertFamily_owner_ne_of_gram_ne_zero
public import Theorems.Thm_BSLambda_PartialAssign_Conflict_symm
public import Theorems.Thm_BSLambda_gram_comm

section
@[expose] public section
namespace BSLambda
namespace CertFamily
open scoped Matrix Matrix.Norms.L2Operator
variable {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]
variable (F : CertFamily V ι)
private theorem dist_ne_one_of_dist_eq_one {x y : Ones F.ind} (hg : gram F.ind x y ≠ 0)
    (hd : (F.P (F.owner y)).dist x.1 = 1) : (F.P (F.owner x)).dist y.1 ≠ 1 := by
  rw [(F.dist_eq_two_of_dist_eq_one hg hd).1]
  omega
private theorem gram_eq_offMat_add_offMat {x y : Ones F.ind} (hxy : x ≠ y) :
    gram F.ind x y = F.offMat x y + F.offMat y x := by
  rw [F.offMat_apply, F.offMat_apply]
  by_cases hgram : gram F.ind x y = 0
  · rw [hgram, ← gram_comm x y, hgram, ite_self, ite_self, add_zero]
  have hown : F.owner x ≠ F.owner y := F.owner_ne_of_gram_ne_zero hxy hgram
  rcases F.dist_eq_one_or_dist_eq_one hxy hgram with hd | hd
  · rw [if_pos ⟨hown, hd⟩, if_neg fun h ↦ F.dist_ne_one_of_dist_eq_one hgram hd h.2,
      add_zero]
  · have hgram' : gram F.ind y x ≠ 0 := gram_comm x y ▸ hgram
    rw [if_neg fun h ↦ F.dist_ne_one_of_dist_eq_one hgram' hd h.2,
      if_pos ⟨hown.symm, hd⟩,
      zero_add, gram_comm]
end CertFamily
end BSLambda
end
end

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.CertFamily
open scoped Matrix Matrix.Norms.L2Operator
variable {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]
variable (F : CertFamily V ι)
namespace BSLambda.CertFamily
theorem _root_.solution : gram F.ind = F.diagMat + F.offMat + F.offMatᵀ := by
  ext x y
  rw [Matrix.add_apply, Matrix.add_apply, Matrix.transpose_apply, F.diagMat_apply]
  by_cases hxy : x = y
  · subst hxy
    rw [if_pos rfl, F.offMat_diag, add_zero, add_zero]
  · rw [if_neg hxy, zero_add]
    exact F.gram_eq_offMat_add_offMat hxy
end BSLambda.CertFamily
