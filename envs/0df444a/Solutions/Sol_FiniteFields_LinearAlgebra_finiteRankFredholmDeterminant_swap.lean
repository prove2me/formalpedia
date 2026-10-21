-- Prove2me | solution 1 for FiniteFields.LinearAlgebra.finiteRankFredholmDeterminant_swap
-- status  : ACCEPTED   (prove)
-- author  : @Idealson
-- created : 2026-10-20T06:51:31.290943+00:00
-- url     : https://prove2.me/submissions/4cd4b730-a290-444c-886e-5886e1abc53c

import Mathlib
import Definitions.Def_FiniteFields_Dwork_TraceFormula
section
noncomputable section
open Module Polynomial PowerSeries
namespace FiniteFields.LinearAlgebra
universe u v w
variable {R : Type u} {M : Type v} [CommRing R]
variable [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
theorem fredholmDeterminant_eq_det (u : Module.End R M) {ι : Type w}
    [Fintype ι] [DecidableEq ι] (b : Basis ι R M) :
    fredholmDeterminant u =
      Matrix.det (1 - (X : R[X]) • (LinearMap.toMatrix b b u).map Polynomial.C) := by
  rw [fredholmDeterminant, ← LinearMap.charpoly_toMatrix u b,
    Matrix.reverse_charpoly, Matrix.charpolyRev]
section FiniteRank
variable {N : Type w} [AddCommGroup N] [Module R N] [Module.Free R N] [Module.Finite R N]
end FiniteRank
end FiniteFields.LinearAlgebra
end
end
open Module Polynomial PowerSeries
open FiniteFields.LinearAlgebra
universe u v w
variable {R : Type u} {M : Type v} [CommRing R]
variable [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
variable {N : Type w} [AddCommGroup N] [Module R N] [Module.Free R N] [Module.Finite R N]
theorem solution (a : M →ₗ[R] N) (b : N →ₗ[R] M) :
    finiteRankFredholmDeterminant a b = finiteRankFredholmDeterminant b a := by
  classical
  let bM := Module.Free.chooseBasis R M
  let bN := Module.Free.chooseBasis R N
  rw [finiteRankFredholmDeterminant, finiteRankFredholmDeterminant,
    fredholmDeterminant_eq_det _ bM, fredholmDeterminant_eq_det _ bN,
    LinearMap.toMatrix_comp bM bN bM b a,
    LinearMap.toMatrix_comp bN bM bN a b]
  let A := LinearMap.toMatrix bM bN a
  let B := LinearMap.toMatrix bN bM b
  simpa [A, B, Matrix.map_mul, Matrix.smul_mul] using
    Matrix.det_one_sub_mul_comm ((X : R[X]) • B.map Polynomial.C) (A.map Polynomial.C)
