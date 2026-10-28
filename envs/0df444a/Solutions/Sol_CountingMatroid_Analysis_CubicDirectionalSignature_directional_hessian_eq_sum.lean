-- Prove2me | solution 1 for CountingMatroid.Analysis.CubicDirectionalSignature.directional_hessian_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T14:47:07.293969+00:00
-- url     : https://prove2.me/submissions/a90fb3ee-25b4-46b1-843f-e187a92b7592

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

set_option backward.isDefEq.respectTransparency false in
/-- INTERNAL: Formal differentiation identifies a directional Hessian with
its nonnegative weighted coordinate Hessians; no spectral closure is used.
TEXLINE: main.tex:340-348 -/
theorem solution {σ : Type} [Fintype σ] [DecidableEq σ]
    (p : MvPolynomial σ ℚ) (d : σ → ℚ) :
    Matrix.toQuadraticForm' (fun i j =>
      ((MvPolynomial.constantCoeff (MvPolynomial.pderiv i (MvPolynomial.pderiv j
        (∑ s, MvPolynomial.C (d s) * MvPolynomial.pderiv s p))) : ℚ) : ℝ)) =
    ∑ s, (d s : ℝ) • Matrix.toQuadraticForm' (fun i j =>
      ((MvPolynomial.constantCoeff (MvPolynomial.pderiv i
        (MvPolynomial.pderiv j (MvPolynomial.pderiv s p))) : ℚ) : ℝ)) := by
  have hm : (fun i j =>
      ((MvPolynomial.constantCoeff (MvPolynomial.pderiv i (MvPolynomial.pderiv j
        (∑ s, MvPolynomial.C (d s) * MvPolynomial.pderiv s p))) : ℚ) : ℝ)) =
      ∑ s, (d s : ℝ) • (fun i j =>
      ((MvPolynomial.constantCoeff (MvPolynomial.pderiv i
        (MvPolynomial.pderiv j (MvPolynomial.pderiv s p))) : ℚ) : ℝ)) := by
    ext i j
    simp
  rw [hm]
  simp only [Matrix.toQuadraticForm', map_sum, map_smul,
    LinearMap.BilinMap.toQuadraticMap_sum, LinearMap.BilinMap.toQuadraticMap_smul]
