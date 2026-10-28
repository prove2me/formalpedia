-- Prove2me | solution 1 for CountingMatroid.Analysis.LorentzianDirectionalSignature.coordinate_pderiv_certificate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T15:53:21.24417+00:00
-- url     : https://prove2.me/submissions/4194bbb8-6d64-4010-a22f-3f0fe538bbfd

import Definitions.Def_CountingMatroid_Analysis_CubicTensorContraction
import Definitions.Def_CountingMatroid_Analysis_LorentzianDirectionalSignature
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
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Instances.Real.Lemmas
import Theorems.Thm_CountingMatroid_Analysis_NonnegativeDirectionalMConvexSupport_nonnegative_directional_mconvex_support

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
namespace CountingMatroid.Analysis.NonnegativeDirectionalMConvexSupport
end CountingMatroid.Analysis.NonnegativeDirectionalMConvexSupport
set_option autoImplicit false

/-!
Coordinate certificates for the Lorentzian argument record homogeneous degree,
nonnegative coefficients, M-convex support, and the positive-signature bound
for every quadratic coordinate derivative. The directional signature theorem
is reduced to two independent obligations: M-convex support preservation under
nonnegative directional differentiation, and the cubic signature mixing step.
The coefficient/support calculations and the reduction through coordinate and
directional derivative lists are implemented. The two imported obligations
remain open, so the general theorem is not yet a completed proof. The original
degree-two proof is preserved.

The paper invokes the Brändén–Huh closure results at main.tex:340-348. The pinned
libraries contain homogeneous partial-derivative and quadratic-signature APIs,
but no applicable Lorentzian or M-convex directional-closure theorem was found.

-/

namespace CountingMatroid.Analysis.LorentzianDirectionalSignature
end CountingMatroid.Analysis.LorentzianDirectionalSignature
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.LorentzianDirectionalSignature

open scoped BigOperators

/-- INTERNAL: Coordinate differentiation preserves the coordinate certificate;
the exchange field uses the separately isolated support-deletion lemma.
TEXLINE: main.tex:340-348 -/
theorem solution {σ : Type} [Fintype σ]
    (p : MvPolynomial σ ℚ) (n : ℕ) (hp : CoordinateLorentzian p n) (s : σ) :
    CoordinateLorentzian (MvPolynomial.pderiv s p) (n - 1) := by
  classical
  refine ⟨hp.homogeneous.pderiv, ?_, ?_, ?_⟩
  · intro m
    rw [MvPolynomial.coeff_pderiv]
    exact mul_nonneg (hp.coeff_nonneg _) (by positivity)
  · have hd : ∀ t : σ, 0 ≤ (Pi.single s (1 : ℚ) : σ → ℚ) t := by
      intro t
      simp only [Pi.single_apply]
      split_ifs <;> norm_num
    have h := NonnegativeDirectionalMConvexSupport.nonnegative_directional_mconvex_support
      p n hp.homogeneous hp.coeff_nonneg hp.exchange (Pi.single s 1) hd
    simpa [HasMConvexSupport, Pi.single_apply] using h
  · intro xs hxs
    have hlen : (xs ++ [s]).length + 2 = n := by
      simp only [List.length_append, List.length_singleton]
      omega
    simpa only [List.foldr_append, List.foldr_cons, List.foldr_nil] using
      hp.coordinate_signature (xs ++ [s]) hlen
