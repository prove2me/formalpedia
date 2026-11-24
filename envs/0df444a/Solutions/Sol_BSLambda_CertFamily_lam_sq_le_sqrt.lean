-- Prove2me | solution 1 for BSLambda.CertFamily.lam_sq_le_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:42:48.886752+00:00
-- url     : https://prove2.me/submissions/ce6f81db-bd5f-484d-846d-08aac1dc0e4d

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_GramClass
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_CertUnion
public import Theorems.Thm_BSLambda_CertFamily_lam_sq_le

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.CertFamily
open scoped Matrix Matrix.Norms.L2Operator
variable {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]
variable (F : CertFamily V ι)
namespace BSLambda.CertFamily
theorem _root_.solution (hc : 1 ≤ F.c) :
    lam F.ind ^ 2 ≤ (F.c : ℝ) + 2 * Real.sqrt (((F.c : ℝ) - 1) * F.A * F.B) := by
  refine F.lam_sq_le.trans_eq ?_
  rw [offBound, Nat.cast_mul, Nat.cast_sub hc, Nat.cast_one]
  ring_nf
end BSLambda.CertFamily
