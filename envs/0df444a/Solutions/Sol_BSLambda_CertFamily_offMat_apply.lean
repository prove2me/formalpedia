-- Prove2me | solution 1 for BSLambda.CertFamily.offMat_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:15:26.567515+00:00
-- url     : https://prove2.me/submissions/b53b5661-6832-4764-a2cb-177e42ec8d69

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
    F.offMat x y =
      if F.owner x ≠ F.owner y ∧ (F.P (F.owner y)).dist x.1 = 1 then gram F.ind x y else 0 :=
  rfl
end BSLambda.CertFamily
