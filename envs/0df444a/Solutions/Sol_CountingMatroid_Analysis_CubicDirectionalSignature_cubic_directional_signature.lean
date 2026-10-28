-- Prove2me | solution 1 for CountingMatroid.Analysis.CubicDirectionalSignature.cubic_directional_signature
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:12:47.205993+00:00
-- url     : https://prove2.me/submissions/9058cc57-7760-45ca-b638-1d370e87c197

import Definitions.Def_CountingMatroid_Analysis_CubicTensorContraction
import Definitions.Def_CountingMatroid_Analysis_QuadraticNonpositiveHyperplane
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Multiset.Count
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.QuadraticForm.Signature
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Instances.Real.Lemmas
import Theorems.Thm_CountingMatroid_Analysis_CubicDirectionalSignature_directional_hessian_eq_sum
import Theorems.Thm_CountingMatroid_Analysis_CubicTensorContraction_cubic_tensor_contraction_hyperplane
import Theorems.Thm_CountingMatroid_Analysis_CubicThirdDerivativeSupport_cubic_third_derivative_support
import Theorems.Thm_CountingMatroid_Analysis_QuadraticSignatureHyperplane_hasNonpositiveHyperplane_of_sigPos_le_one

namespace CountingMatroid.Analysis.CubicDirectionalSignature
end CountingMatroid.Analysis.CubicDirectionalSignature
namespace CountingMatroid.Analysis.CubicTensorRayleighContraction
end CountingMatroid.Analysis.CubicTensorRayleighContraction
namespace CountingMatroid.Analysis.NonnegativeContractionLimit
end CountingMatroid.Analysis.NonnegativeContractionLimit
namespace CountingMatroid.Analysis.QuadraticHyperplanePointwiseLimit
end CountingMatroid.Analysis.QuadraticHyperplanePointwiseLimit
namespace CountingMatroid.Analysis.ConnectedRayleighHyperplane
end CountingMatroid.Analysis.ConnectedRayleighHyperplane
namespace CountingMatroid.Analysis.ConnectedNormalizedRayleigh
end CountingMatroid.Analysis.ConnectedNormalizedRayleigh
namespace CountingMatroid.Analysis.ConnectedLaplacianKernel
end CountingMatroid.Analysis.ConnectedLaplacianKernel
namespace CountingMatroid.Analysis.RayleighFixedKernel
end CountingMatroid.Analysis.RayleighFixedKernel
namespace CountingMatroid.Analysis.QuadraticSignatureHyperplane
end CountingMatroid.Analysis.QuadraticSignatureHyperplane
namespace CountingMatroid.Analysis.CubicExchangeCut
end CountingMatroid.Analysis.CubicExchangeCut
namespace CountingMatroid.Analysis.CubicThirdDerivativeSupport
end CountingMatroid.Analysis.CubicThirdDerivativeSupport
section


set_option autoImplicit false

/-!
A quadratic form is nonpositive on a hyperplane if some real linear
functional has a nonpositive kernel. This property survives linear pullback
and nonnegative scaling. It implies the signature bound, and also gives
nonpositivity on the orthogonal complement of any positive vector.
No property of matroid polynomials is assumed or asserted here.
-/

namespace CountingMatroid.Analysis.QuadraticNonpositiveHyperplane







/-- INTERNAL: Rank-nullity converts the hyperplane witness to the exact
positive-signature bound used for quadratic descendants.
TEXLINE: main.tex:326-348 -/
theorem HasNonpositiveHyperplane.sigPos_le_one {V : Type}
    [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    {Q : QuadraticForm ℝ V} (hQ : HasNonpositiveHyperplane Q) : sigPos Q ≤ 1 := by
  obtain ⟨l, hl⟩ := hQ
  have hdim := QuadraticForm.sigPos_add_finrank_le_of_nonpos
    (V := LinearMap.ker l) (fun v hv => hl v (LinearMap.mem_ker.mp hv))
  have hnull := l.finrank_range_add_finrank_ker
  have hrange : Module.finrank ℝ (LinearMap.range l) ≤ 1 := by
    simpa using (LinearMap.range l).finrank_le
  omega



end CountingMatroid.Analysis.QuadraticNonpositiveHyperplane

end
set_option autoImplicit false

/-!
The cubic step in directional Lorentzian closure. This isolates the spectral
obligation from support preservation: the constant Hessians of the coordinate
derivatives of a cubic arise from one symmetric nonnegative cubic tensor.
The polynomial support is identified with the tensor's unordered triples by
`CubicThirdDerivativeSupport`. The directional signature then follows from
the tensor contraction boundary in `CubicTensorContraction`, whose general
spectral proof remains open. No closure of arbitrary sums is asserted.
-/

namespace CountingMatroid.Analysis.CubicDirectionalSignature
end CountingMatroid.Analysis.CubicDirectionalSignature
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.CubicDirectionalSignature

open scoped BigOperators
open QuadraticNonpositiveHyperplane QuadraticSignatureHyperplane

/-- INTERNAL: The cubic mixing step suffices for directional closure at every
degree, by first taking coordinate derivatives down to degree three.
TEXLINE: main.tex:340-348 -/
theorem solution {σ : Type} [Fintype σ] [DecidableEq σ]
    (p : MvPolynomial σ ℚ) (hhom : p.IsHomogeneous 3)
    (hp : ∀ m, 0 ≤ p.coeff m)
    (hex : ∀ x ∈ p.support, ∀ y ∈ p.support, ∀ i, y i < x i →
      ∃ j, x j < y j ∧
        x - Finsupp.single i 1 + Finsupp.single j 1 ∈ p.support)
    (hsig : ∀ s, sigPos (Matrix.toQuadraticForm' (fun i j =>
      ((MvPolynomial.constantCoeff (MvPolynomial.pderiv i
        (MvPolynomial.pderiv j (MvPolynomial.pderiv s p))) : ℚ) : ℝ))) ≤ 1)
    (d : σ → ℚ) (hd : ∀ s, 0 ≤ d s) :
    sigPos (Matrix.toQuadraticForm' (fun i j =>
      ((MvPolynomial.constantCoeff (MvPolynomial.pderiv i (MvPolynomial.pderiv j
        (∑ s, MvPolynomial.C (d s) * MvPolynomial.pderiv s p))) : ℚ) : ℝ))) ≤ 1 := by
  classical
  let T : σ → σ → σ → ℚ := fun s i j =>
    MvPolynomial.constantCoeff (MvPolynomial.pderiv i
      (MvPolynomial.pderiv j (MvPolynomial.pderiv s p)))
  have hderiv (f : MvPolynomial σ ℚ) (hf : ∀ m, 0 ≤ f.coeff m)
      (s : σ) (m : σ →₀ ℕ) : 0 ≤ (MvPolynomial.pderiv s f).coeff m := by
    rw [MvPolynomial.coeff_pderiv]
    exact mul_nonneg (hf _) (by positivity)
  have hT : ∀ s i j, 0 ≤ T s i j := by
    intro s i j
    exact hderiv _ (hderiv _ (hderiv p hp s) j) i 0
  have hswap : ∀ s i j, T s i j = T i s j := by
    intro s i j
    simp only [T, MvPolynomial.constantCoeff_eq, MvPolynomial.coeff_pderiv,
      zero_add, Finsupp.zero_apply, Nat.cast_zero, zero_add, mul_one]
    by_cases hsi : s = i <;> by_cases hsj : s = j <;> by_cases hij : i = j <;>
      simp_all [Finsupp.add_apply, add_comm, add_left_comm, mul_comm, mul_left_comm]
  have hlast : ∀ s i j, T s i j = T s j i := by
    intro s i j
    simp only [T, MvPolynomial.constantCoeff_eq, MvPolynomial.coeff_pderiv,
      zero_add, Finsupp.zero_apply, Nat.cast_zero, zero_add, mul_one]
    by_cases hij : i = j
    · subst j
      rfl
    · simp [Finsupp.add_apply, hij, Ne.symm hij, add_comm,
        mul_comm, mul_left_comm]
  have hsupp (m : σ →₀ ℕ) :
      m ∈ CubicTensorContraction.cubicTensorSupport T ↔ m ∈ p.support :=
    (CubicThirdDerivativeSupport.cubic_third_derivative_support p hhom m).symm
  have hTex : ∀ x ∈ CubicTensorContraction.cubicTensorSupport T,
      ∀ y ∈ CubicTensorContraction.cubicTensorSupport T, ∀ i, y i < x i →
      ∃ j, x j < y j ∧ x - Finsupp.single i 1 + Finsupp.single j 1 ∈
        CubicTensorContraction.cubicTensorSupport T := by
    intro x hx y hy i hi
    obtain ⟨j, hj, hm⟩ := hex x ((hsupp x).mp hx) y ((hsupp y).mp hy) i hi
    exact ⟨j, hj, (hsupp _).mpr hm⟩
  have hplanes : ∀ s, HasNonpositiveHyperplane (Matrix.toQuadraticForm' (fun i j =>
      ((MvPolynomial.constantCoeff (MvPolynomial.pderiv i
        (MvPolynomial.pderiv j (MvPolynomial.pderiv s p))) : ℚ) : ℝ))) :=
    fun s => hasNonpositiveHyperplane_of_sigPos_le_one _ (hsig s)
  rw [directional_hessian_eq_sum]
  apply HasNonpositiveHyperplane.sigPos_le_one
  exact CubicTensorContraction.cubic_tensor_contraction_hyperplane T hT hswap hlast
    hTex hplanes d hd
