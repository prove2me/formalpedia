-- Prove2me | solution 1 for BSLambda.CertFamily.card_offMat_row_slice_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:26:52.764397+00:00
-- url     : https://prove2.me/submissions/80780e4e-4dd1-46f5-9682-7a16321bc0af

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_GramClass
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_CertUnion
public import Theorems.Thm_BSLambda_CertFamily_offMat_ne_zero_iff
public import Theorems.Thm_BSLambda_CertFamily_exists_flip_proj
public import Theorems.Thm_BSLambda_CertFamily_exists_flip_proj_self
public import Theorems.Thm_BSLambda_CertFamily_owner_sat
public import Theorems.Thm_BSLambda_PartialAssign_Conflict_symm
public import Theorems.Thm_BSLambda_PartialAssign_codim_eq_card_fixedSet
public import Theorems.Thm_Set_PairwiseDisjoint_injOn


set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.CertFamily
open scoped Matrix Matrix.Norms.L2Operator
variable {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]
variable (F : CertFamily V ι)
namespace BSLambda.CertFamily
theorem _root_.solution {x : Ones F.ind} {j : ι} (hj : j ≠ F.owner x)
    (hd : (F.P j).dist x.1 = 1) :
    (Finset.univ.filter fun y : Ones F.ind =>
      F.offMat x y ≠ 0 ∧ F.owner y = j).card ≤ F.c - 1 := by
  obtain ⟨p₀, hp₀mem, hp₀eq⟩ := F.exists_flip_proj_self (Ne.symm hj) (F.owner_sat x) hd
  have hmaps : ∀ y ∈ (Finset.univ.filter fun y : Ones F.ind ↦
        F.offMat x y ≠ 0 ∧ F.owner y = j), y.1 ∈
      ((F.P (F.owner x)).fixedSet.erase p₀).image fun p ↦ flipSet ((F.P j).proj x.1) {p} := by
    intro y hy
    rw [Finset.mem_filter_univ] at hy
    obtain ⟨hown, hdist, hgram⟩ := F.offMat_ne_zero_iff.1 hy.1
    have hxy : x ≠ y := ne_of_apply_ne F.owner hown
    obtain ⟨p, hpmem, hpeq⟩ := F.exists_flip_proj hgram hdist
    rw [hy.2] at hpeq
    refine Finset.mem_image.2 ⟨p, Finset.mem_erase.2 ⟨?_, hpmem⟩, hpeq.symm⟩
    rintro rfl
    exact hxy (Subtype.ext (hp₀eq.trans hpeq.symm))
  refine (Finset.card_le_card_of_injOn Subtype.val hmaps
    Subtype.coe_injective.injOn).trans (Finset.card_image_le.trans (le_of_eq ?_))
  rw [Finset.card_erase_of_mem hp₀mem, ← PartialAssign.codim_eq_card_fixedSet,
    F.codim_eq (F.owner x)]
end BSLambda.CertFamily
