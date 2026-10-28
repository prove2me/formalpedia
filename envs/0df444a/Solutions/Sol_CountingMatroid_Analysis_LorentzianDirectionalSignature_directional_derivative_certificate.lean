-- Prove2me | solution 1 for CountingMatroid.Analysis.LorentzianDirectionalSignature.directional_derivative_certificate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:14:30.149978+00:00
-- url     : https://prove2.me/submissions/fef6496b-f8ac-4838-b50d-e79e319bbdcf

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
import Theorems.Thm_CountingMatroid_Analysis_CubicDirectionalSignature_cubic_directional_signature
import Theorems.Thm_CountingMatroid_Analysis_LorentzianDirectionalSignature_coordinate_pderiv_certificate
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
section


set_option autoImplicit false

/-!
Support calculations for a nonnegative directional derivative. Its coefficients
are nonnegative, and its support consists precisely of exponents obtained by
removing a unit in a direction with positive weight. The exchange condition
is preserved by a finite exchange argument on these lifted exponents.
-/

namespace CountingMatroid.Analysis.NonnegativeDirectionalMConvexSupport

open scoped BigOperators

/-- INTERNAL: Nonnegative directional differentiation has no coefficient cancellation.
TEXLINE: main.tex:340-348 -/
theorem directional_coeff_nonnegative {σ : Type} [Fintype σ]
    (p : MvPolynomial σ ℚ) (hp : ∀ m, 0 ≤ p.coeff m)
    (d : σ → ℚ) (hd : ∀ s, 0 ≤ d s) (m : σ →₀ ℕ) :
    0 ≤ (∑ s, MvPolynomial.C (d s) * MvPolynomial.pderiv s p).coeff m := by
  classical
  rw [MvPolynomial.coeff_sum]
  apply Finset.sum_nonneg
  intro s _
  rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_pderiv]
  exact mul_nonneg (hd s) (mul_nonneg (hp _) (by positivity))





end CountingMatroid.Analysis.NonnegativeDirectionalMConvexSupport

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · proved · closed directional support exchange by lifting support witnesses and using at most three original-support exchanges; no new proof obligations.
-/

end

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











/-- INTERNAL: The coordinate certificate descends through a list of partial
derivatives, with the degree decreased by the list's length.
TEXLINE: main.tex:340-348 -/
theorem coordinate_fold_certificate {σ : Type} [Fintype σ]
    (p : MvPolynomial σ ℚ) (n : ℕ) (hp : CoordinateLorentzian p n) (xs : List σ) :
    CoordinateLorentzian (xs.foldr (fun s f => MvPolynomial.pderiv s f) p)
      (n - xs.length) := by
  induction xs generalizing n with
  | nil => simpa using hp
  | cons s xs ih =>
    have h := coordinate_pderiv_certificate _ (n - xs.length) (ih n hp) s
    simpa only [List.foldr_cons, List.length_cons, Nat.sub_sub] using h

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

/-- INTERNAL: A coordinate derivative list commutes with a rational directional
derivative, allowing the signature field to be checked on cubic derivatives.
TEXLINE: main.tex:340-348 -/
theorem coordinate_fold_directional_commute {σ : Type} [Fintype σ]
    (xs : List σ) (p : MvPolynomial σ ℚ) (d : σ → ℚ) :
    xs.foldr (fun s f => MvPolynomial.pderiv s f)
      (∑ s, MvPolynomial.C (d s) * MvPolynomial.pderiv s p) =
    ∑ s, MvPolynomial.C (d s) * MvPolynomial.pderiv s
      (xs.foldr (fun s f => MvPolynomial.pderiv s f) p) := by
  classical
  induction xs with
  | nil => rfl
  | cons i xs ih =>
    simp only [List.foldr_cons, ih, map_sum, MvPolynomial.pderiv_C_mul]
    simp only [coordinate_pderiv_commute _ i]







end CountingMatroid.Analysis.LorentzianDirectionalSignature

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · validated parallel handoff · request agent1-directional-cubic-support-20261009-1 accepted at semantic-use stage; NonnegativeDirectionalMConvexSupport and CubicDirectionalSignature transferred to scheduler ownership. The unchanged target has a complete proof body using both children; its remaining mathematical proof debt is explicitly retained in those two open obligations.
* 2026-10-09 · decomposed · directional signature reduced to independently stated support-exchange preservation and cubic signature mixing; proved coefficient positivity, exact directional support membership, coordinate commutation, and the parent reduction. The two child obligations remain open pending live handoff.
* 2026-10-09 · blocked · preserved the degree-two proof; statement-shape searches of pinned Mathlib and Arlib found no Lorentzian directional closure result. Stdin applications of the degree-two and hyperplane bounds exposed, respectively, a degree-two certificate/length mismatch and a missing common nonpositive hyperplane. Proposed the unchanged borrowed directional signature declaration as prior input; added no helper, assumption, or import.
-/

end
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

/-- INTERNAL: Support preservation and cubic mixing together preserve the
coordinate certificate under one nonnegative directional derivative.
TEXLINE: main.tex:340-348 -/
theorem solution {σ : Type} [Fintype σ]
    (p : MvPolynomial σ ℚ) (k : ℕ) (hp : CoordinateLorentzian p (k + 3))
    (d : σ → ℚ) (hd : ∀ s, 0 ≤ d s) :
    CoordinateLorentzian
      (∑ s, MvPolynomial.C (d s) * MvPolynomial.pderiv s p) (k + 2) := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply MvPolynomial.IsHomogeneous.sum
    intro s _
    simpa using hp.homogeneous.pderiv.C_mul (d s)
  · exact NonnegativeDirectionalMConvexSupport.directional_coeff_nonnegative p
      hp.coeff_nonneg d hd
  · exact NonnegativeDirectionalMConvexSupport.nonnegative_directional_mconvex_support
      p (k + 3) hp.homogeneous hp.coeff_nonneg hp.exchange d hd
  · intro xs hxs
    have hdegree : k + 3 - xs.length = 3 := by omega
    have hcert := coordinate_fold_certificate p (k + 3) hp xs
    rw [hdegree] at hcert
    rw [coordinate_fold_directional_commute]
    exact CubicDirectionalSignature.cubic_directional_signature _ hcert.homogeneous
      hcert.coeff_nonneg hcert.exchange
      (fun s => hcert.coordinate_signature [s] rfl) d hd
