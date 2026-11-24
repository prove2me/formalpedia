-- Prove2me | solution 1 for BSLambda.CertFamily.card_offMat_row_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:27:53.352064+00:00
-- url     : https://prove2.me/submissions/eef23944-63d2-4afb-8e9b-1d33d7a2c093

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_GramClass
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_CertUnion
public import Theorems.Thm_BSLambda_CertFamily_offMat_ne_zero_iff
public import Theorems.Thm_BSLambda_CertFamily_card_offMat_row_slice_le
public import Theorems.Thm_BSLambda_CertFamily_owner_sat
public import Theorems.Thm_BSLambda_PartialAssign_Conflict_symm


set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.CertFamily
open scoped Matrix Matrix.Norms.L2Operator
variable {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]
variable (F : CertFamily V ι)
namespace BSLambda.CertFamily
theorem _root_.solution (x : Ones F.ind) :
    (Finset.univ.filter fun y : Ones F.ind => F.offMat x y ≠ 0).card
      ≤ F.A * (F.c - 1) := by
  have hmaps : ∀ y ∈ (Finset.univ.filter fun y : Ones F.ind ↦ F.offMat x y ≠ 0),
      F.owner y ∈ Finset.univ.filter fun j ↦ j ≠ F.owner x ∧ (F.P j).dist x.1 = 1 := by
    intro y hy
    rw [Finset.mem_filter_univ] at hy ⊢
    obtain ⟨hown, hdist, -⟩ := F.offMat_ne_zero_iff.1 hy
    exact ⟨Ne.symm hown, hdist⟩
  have hslice : ∀ j ∈ Finset.univ.filter fun j ↦ j ≠ F.owner x ∧ (F.P j).dist x.1 = 1,
      ((Finset.univ.filter fun y : Ones F.ind ↦ F.offMat x y ≠ 0).filter
        fun y ↦ F.owner y = j).card ≤ F.c - 1 := by
    intro j hj
    rw [Finset.mem_filter_univ] at hj
    rw [Finset.filter_filter]
    exact F.card_offMat_row_slice_le hj.1 hj.2
  refine (Finset.card_le_mul_card_image_of_maps_to hmaps _ hslice).trans ?_
  rw [mul_comm]
  exact Nat.mul_le_mul_right _ (F.listOne (F.owner x) x.1 (F.owner_sat x))
end BSLambda.CertFamily
