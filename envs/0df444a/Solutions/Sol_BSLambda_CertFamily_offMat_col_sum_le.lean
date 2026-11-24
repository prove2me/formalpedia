-- Prove2me | solution 1 for BSLambda.CertFamily.offMat_col_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:28:03.958338+00:00
-- url     : https://prove2.me/submissions/13ceed7d-ba7d-4468-9790-caf5a4018068

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_GramClass
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_CertUnion
public import Theorems.Thm_Finset_sum_le_card_filter_ne_zero
public import Theorems.Thm_BSLambda_CertFamily_offMat_le_one
public import Theorems.Thm_BSLambda_CertFamily_card_offMat_col_le

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.CertFamily
open scoped Matrix Matrix.Norms.L2Operator
variable {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]
variable (F : CertFamily V ι)
namespace BSLambda.CertFamily
theorem _root_.solution (y : Ones F.ind) :
    ∑ x, F.offMat x y ≤ (F.B : ℝ) :=
  (Finset.sum_le_card_filter_ne_zero _ fun x _ ↦ F.offMat_le_one x y).trans
    (by exact_mod_cast F.card_offMat_col_le y)
end BSLambda.CertFamily
