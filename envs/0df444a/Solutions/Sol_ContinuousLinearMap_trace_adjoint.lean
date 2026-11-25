-- Prove2me | solution 1 for ContinuousLinearMap.trace_adjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:06:13.112822+00:00
-- url     : https://prove2.me/submissions/e2fba613-3434-456e-a6b9-c01d2029c073

module
public import Mathlib.Analysis.Convex.Cone.Extension
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.Trace
public import Mathlib.Analysis.LocallyConvex.HahnBanach
public import Mathlib.Analysis.Normed.Module.Span
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Definitions.Def_BasicResults_JohnIngredients

set_option autoImplicit true
@[expose] public section
public section
open scoped InnerProductSpace ComplexConjugate
open ContinuousLinearMap
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E] [CompleteSpace E]
namespace ContinuousLinearMap
theorem _root_.solution (G : E →L[𝕜] E) :
    LinearMap.trace 𝕜 E ((ContinuousLinearMap.adjoint G : E →L[𝕜] E) : E →ₗ[𝕜] E)
      = starRingEnd 𝕜 (LinearMap.trace 𝕜 E (G : E →ₗ[𝕜] E)) := by
  rw [LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis 𝕜 E),
    LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis 𝕜 E), map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ContinuousLinearMap.coe_coe, ContinuousLinearMap.coe_coe,
    ContinuousLinearMap.adjoint_inner_right]
  exact (inner_conj_symm _ _).symm
end ContinuousLinearMap
