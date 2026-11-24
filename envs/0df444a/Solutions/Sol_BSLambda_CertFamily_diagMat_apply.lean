-- Prove2me | solution 1 for BSLambda.CertFamily.diagMat_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:22:54.358802+00:00
-- url     : https://prove2.me/submissions/fca7dfea-3985-48a1-984b-6b8f4de35d74

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_GramClass
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_CertUnion

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.CertFamily
open scoped Matrix Matrix.Norms.L2Operator
variable {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]
variable (F : CertFamily V ι)
namespace BSLambda.CertFamily
theorem _root_.solution (x y : Ones F.ind) :
    F.diagMat x y = if x = y then gram F.ind x x else 0 :=
  Matrix.diagonal_apply _ _ _
end BSLambda.CertFamily
