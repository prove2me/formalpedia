-- Prove2me | solution 1 for BSLambda.CertFamily.offMat_row_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:28:51.656262+00:00
-- url     : https://prove2.me/submissions/ca94a952-26ca-4ef3-b099-cd94073f6211

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_GramClass
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_CertUnion
public import Theorems.Thm_Finset_sum_le_card_filter_ne_zero
public import Theorems.Thm_BSLambda_CertFamily_offMat_le_one
public import Theorems.Thm_BSLambda_CertFamily_card_offMat_row_le

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
    ∑ y, F.offMat x y ≤ ((F.A * (F.c - 1) : ℕ) : ℝ) :=
  (Finset.sum_le_card_filter_ne_zero _ fun y _ ↦ F.offMat_le_one x y).trans
    (by exact_mod_cast F.card_offMat_row_le x)
end BSLambda.CertFamily
