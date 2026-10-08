-- Prove2me | solution 1 for CurveSymmetry.criticalZero_transport
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T12:56:29.998498+00:00
-- url     : https://prove2.me/submissions/d5319cb9-ea0a-42d7-aaec-70b608c12f46

-- Solution generated from lean/HomogeneousDifferential.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Affine.MazurUlam
import Mathlib.Data.Complex.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine

section
open CurveSymmetry
set_option autoImplicit false
theorem solution {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (T : E ≃L[𝕜] E) {F G : E → 𝕜} {k : 𝕜} (hk : k ≠ 0)
    (he : ∀ x, G (T x) = k * F x) (x : E) :
    CriticalZero G (T x) ↔ CriticalZero F x := by
  have hfun : G ∘ T = fun y => k * F y := funext he
  have hd : HasFDerivAt (G ∘ T) (0 : E →L[𝕜] 𝕜) x ↔
      HasFDerivAt G (0 : E →L[𝕜] 𝕜) (T x) := by
    simpa using (T.comp_right_hasFDerivAt_iff (f := G) (f' := (0 : E →L[𝕜] 𝕜)))
  constructor
  · rintro ⟨hz, hder⟩
    refine ⟨(mul_eq_zero.mp ((he x).symm.trans hz)).resolve_left hk, ?_⟩
    have h := (hd.mpr hder).const_mul k⁻¹
    rw [hfun] at h
    convert h using 1 <;> first | rfl | (ext v; simp [inv_mul_cancel_left₀ hk])
  · rintro ⟨hz, hder⟩
    refine ⟨by rw [he, hz, mul_zero], hd.mp ?_⟩
    rw [hfun]
    convert hder.const_mul k using 1 <;> first | rfl | (ext v; simp)
end

#print axioms solution
