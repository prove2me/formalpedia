-- Prove2me | solution 1 for CountingMatroid.Analysis.SquarefreeCoordinateHessian.coordinate_monomial_zero_of_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T14:45:05.377697+00:00
-- url     : https://prove2.me/submissions/bc1480d7-9900-4935-8c5d-631d9682963f

import Definitions.Def_CountingMatroid_Analysis_CubicTensorContraction
import Definitions.Def_CountingMatroid_Analysis_LorentzianDirectionalSignature
import Definitions.Def_CountingMatroid_Analysis_QuadraticNonpositiveHyperplane
import Definitions.Def_CountingMatroid_Analysis_RankWeightSupportExchange
import Definitions.Def_CountingMatroid_Analysis_SquarefreeCoordinateHessian
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Fintype.Powerset
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

namespace CountingMatroid.Analysis.SquarefreeFullDerivative
end CountingMatroid.Analysis.SquarefreeFullDerivative
namespace CountingMatroid.Analysis.BinaryRankWeightSignature
end CountingMatroid.Analysis.BinaryRankWeightSignature
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
section


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

open scoped BigOperators













/-- INTERNAL: Rational polynomial partial derivatives commute coefficientwise.
TEXLINE: main.tex:340-348 -/
theorem coordinate_pderiv_commute {σ : Type} (p : MvPolynomial σ ℚ) (i j : σ) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv j p) =
      MvPolynomial.pderiv j (MvPolynomial.pderiv i p) := by
  classical
  ext m
  simp only [MvPolynomial.coeff_pderiv]
  by_cases hij : i = j
  · subst j
    rfl
  · simp [Finsupp.add_apply, hij, Ne.symm hij,
      add_comm, add_left_comm, mul_assoc, mul_comm, mul_left_comm]









end CountingMatroid.Analysis.LorentzianDirectionalSignature

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · validated parallel handoff · request agent1-directional-cubic-support-20261009-1 accepted at semantic-use stage; NonnegativeDirectionalMConvexSupport and CubicDirectionalSignature transferred to scheduler ownership. The unchanged target has a complete proof body using both children; its remaining mathematical proof debt is explicitly retained in those two open obligations.
* 2026-10-09 · decomposed · directional signature reduced to independently stated support-exchange preservation and cubic signature mixing; proved coefficient positivity, exact directional support membership, coordinate commutation, and the parent reduction. The two child obligations remain open pending live handoff.
* 2026-10-09 · blocked · preserved the degree-two proof; statement-shape searches of pinned Mathlib and Arlib found no Lorentzian directional closure result. Stdin applications of the degree-two and hyperplane bounds exposed, respectively, a degree-two certificate/length mismatch and a missing common nonpositive hyperplane. Proposed the unchanged borrowed directional signature declaration as prior input; added no helper, assumption, or import.
-/

end

section


set_option autoImplicit false

/-! Coordinate differentiation of a homogeneous polynomial whose label
variables are squarefree reduces its constant Hessian to a residual matrix.
The matrix records the selected labels and the number of homogenizer
derivatives. This calculation concerns arbitrary subset coefficients and
does not assume a matroid signature bound. -/

namespace CountingMatroid.Analysis.SquarefreeCoordinateHessian

open scoped BigOperators
open LorentzianDirectionalSignature





/-- INTERNAL: A coordinate derivative commutes through a list of coordinate
derivatives, allowing a monomial induction to differentiate its input first. -/
theorem coordinate_fold_pderiv_commute {σ : Type} (xs : List σ) (s : σ)
    (p : MvPolynomial σ ℚ) :
    MvPolynomial.pderiv s (xs.foldr (fun t f => MvPolynomial.pderiv t f) p) =
      xs.foldr (fun t f => MvPolynomial.pderiv t f) (MvPolynomial.pderiv s p) := by
  induction xs with
  | nil => rfl
  | cons t xs ih =>
    simp only [List.foldr_cons]
    rw [coordinate_pderiv_commute, ih]







end CountingMatroid.Analysis.SquarefreeCoordinateHessian

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · proved · closed the coordinate Hessian identity using the full-derivative coefficient formula; all four entries have the common homogenizer factorial, and repeated labels give zero.

* 2026-10-09 · partial · after live handoff deferral, proved coordinate-fold commutation and monomial annihilation when a derivative count exceeds its exponent. This closes the normal form for repeated labels anywhere in the list. Only the distinct-label factorial coefficient identity remains open.
* 2026-10-09 · decomposed · defined the exact residual Hessian and proved the derivative-list cardinality identity; instantiated the distinct-label witnesses and reduced the normal form to monomial coefficient extraction. Repeated-label annihilation remains part of the same polynomial obligation.
-/

end
set_option autoImplicit false

/-! Coordinate differentiation of a homogeneous polynomial whose label
variables are squarefree reduces its constant Hessian to a residual matrix.
The matrix records the selected labels and the number of homogenizer
derivatives. This calculation concerns arbitrary subset coefficients and
does not assume a matroid signature bound. -/

namespace CountingMatroid.Analysis.SquarefreeCoordinateHessian
end CountingMatroid.Analysis.SquarefreeCoordinateHessian
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.SquarefreeCoordinateHessian

open scoped BigOperators
open LorentzianDirectionalSignature

/-- INTERNAL: Too many coordinate derivatives annihilate a monomial, even
when derivatives in other coordinates separate the repeated ones. -/
theorem solution {σ : Type} [DecidableEq σ]
    [BEq σ] [LawfulBEq σ]
    (xs : List σ) (a : σ) (m : σ →₀ ℕ) (c : ℚ) (h : m a < xs.count a) :
    xs.foldr (fun t f => MvPolynomial.pderiv t f) (MvPolynomial.monomial m c) = 0 := by
  have hz : ∀ ys : List σ,
      ys.foldr (fun t f => MvPolynomial.pderiv t f) (0 : MvPolynomial σ ℚ) = 0 := by
    intro ys
    induction ys with
    | nil => rfl
    | cons t ys ih => simp [ih]
  induction xs generalizing m c with
  | nil => simp at h
  | cons s xs ih =>
    rw [List.foldr_cons, coordinate_fold_pderiv_commute, MvPolynomial.pderiv_monomial]
    by_cases hs : m s = 0
    · simpa [hs] using hz xs
    · apply ih
      by_cases hsa : s = a
      · subst s
        simp only [List.count_cons_self, Finsupp.tsub_apply, Finsupp.single_eq_same] at *
        omega
      · simpa [List.count_cons, Finsupp.tsub_apply, Finsupp.single_apply,
          hsa, Ne.symm hsa] using h
