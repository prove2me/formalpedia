-- Prove2me | solution 1 for CountingMatroid.Analysis.MixedDirectionalRankWeightSignature.mixed_directional_rank_weight_nonpositive_hyperplane
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:16:08.728637+00:00
-- url     : https://prove2.me/submissions/07b63b77-3a2b-42b4-8174-e348128410ed

import Definitions.Def_CountingMatroid_Analysis_CubicTensorContraction
import Definitions.Def_CountingMatroid_Analysis_LorentzianDirectionalSignature
import Definitions.Def_CountingMatroid_Analysis_QuadraticNonpositiveHyperplane
import Definitions.Def_CountingMatroid_Analysis_RankWeightSupportExchange
import Definitions.Def_CountingMatroid_Analysis_SquarefreeCoordinateHessian
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Order.Chebyshev
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
import Theorems.Thm_CountingMatroid_Analysis_BinaryRankWeightSignature_binary_tutte_nonpositive_hyperplane
import Theorems.Thm_CountingMatroid_Analysis_LorentzianDirectionalSignature_directional_derivative_certificate
import Theorems.Thm_CountingMatroid_Analysis_QuadraticSignatureHyperplane_hasNonpositiveHyperplane_of_sigPos_le_one
import Theorems.Thm_CountingMatroid_Analysis_RankWeightCoordinateLorentzian_rank_weight_basic_invariants
import Theorems.Thm_CountingMatroid_Analysis_RankWeightCoordinateSignature_rank_weight_coordinate_signature
import Theorems.Thm_CountingMatroid_Analysis_RankWeightSupportExchange_rank_weight_support_exchange

namespace CountingMatroid.Analysis.MixedDirectionalRankWeightSignature
end CountingMatroid.Analysis.MixedDirectionalRankWeightSignature
namespace CountingMatroid.Analysis.RankWeightCoordinateLorentzian
end CountingMatroid.Analysis.RankWeightCoordinateLorentzian
namespace CountingMatroid.Analysis.RankWeightCoordinateSignature
end CountingMatroid.Analysis.RankWeightCoordinateSignature
namespace CountingMatroid.Analysis.RankWeightResidualSignature
end CountingMatroid.Analysis.RankWeightResidualSignature
namespace CountingMatroid.Analysis.RankWeightClosurePair
end CountingMatroid.Analysis.RankWeightClosurePair
namespace CountingMatroid.Analysis.ClosureClassQuadraticBound
end CountingMatroid.Analysis.ClosureClassQuadraticBound
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







/-- INTERNAL: At degree two the coordinate certificate already contains the
required Hessian bound; there are no directional derivatives left to take.
TEXLINE: main.tex:340-348 -/
theorem degree_two_directional_signature {σ : Type} [Fintype σ]
    (p : MvPolynomial σ ℚ) (hp : CoordinateLorentzian p 2)
    (ds : List (σ → ℚ)) (hlength : ds.length + 2 = 2) :
    sigPos (constantHessianForm
      (ds.foldr (fun d f => ∑ s, MvPolynomial.C (d s) * MvPolynomial.pderiv s f) p)) ≤ 1 := by
  have hnil : ds = [] := by
    apply List.eq_nil_iff_length_eq_zero.mpr
    omega
  subst ds
  exact hp.coordinate_signature [] rfl











/-- INTERNAL: Iterating one-step directional closure leaves the degree
specified by the remaining coordinate certificate.
TEXLINE: main.tex:340-348 -/
theorem directional_fold_certificate {σ : Type} [Fintype σ]
    (p : MvPolynomial σ ℚ) (ds : List (σ → ℚ)) (k : ℕ)
    (hp : CoordinateLorentzian p (ds.length + k + 2))
    (hds : ∀ d ∈ ds, ∀ s, 0 ≤ d s) :
    CoordinateLorentzian
      (ds.foldr (fun d f => ∑ s, MvPolynomial.C (d s) * MvPolynomial.pderiv s f) p)
      (k + 2) := by
  induction ds generalizing k with
  | nil => simpa using hp
  | cons d ds ih =>
    have hp' : CoordinateLorentzian p (ds.length + (k + 1) + 2) := by
      simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hp
    have htail := ih (k + 1) hp' (fun e he => hds e (List.mem_cons_of_mem d he))
    exact directional_derivative_certificate _ k
      (by simpa only [Nat.add_assoc] using htail)
      d (hds d (List.mem_cons_self))

/-- PAPER: main.tex:340-348
The nonnegative directional-closure consequence of the Lorentzian coordinate
certificate, specialized to rational coefficients and a quadratic result.
BORROWED: Brändén–Huh, Lorentzian polynomials (2020), Theorems 2.10 and
Corollary 2.11, with the defining quadratic signature property. -/
theorem directional_hessian_sigPos_le_one {σ : Type} [Fintype σ]
    (p : MvPolynomial σ ℚ) (n : ℕ) (hp : CoordinateLorentzian p n)
    (ds : List (σ → ℚ)) (hds : ∀ d ∈ ds, ∀ s, 0 ≤ d s)
    (hlength : ds.length + 2 = n) :
    sigPos (constantHessianForm
      (ds.foldr (fun d f => ∑ s, MvPolynomial.C (d s) * MvPolynomial.pderiv s f) p)) ≤ 1 := by
  by_cases hn : n = 2
  · rw [hn] at hp hlength
    exact degree_two_directional_signature p hp ds hlength
  · have hp' : CoordinateLorentzian p (ds.length + 0 + 2) := by
      simpa only [Nat.add_zero, hlength] using hp
    exact (directional_fold_certificate p ds 0 hp' hds).coordinate_signature [] rfl

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

/-!
The matroid-specific coordinate certificate needed by the general Lorentzian
directional-closure theorem. Homogeneity and coefficient nonnegativity are
proved directly. Support exchange is proved in RankWeightSupportExchange
using the exact subset description of the support. The remaining coordinate
quadratic signatures are isolated in RankWeightCoordinateSignature, with the
cases of ground size at most two and two repeated leading label derivatives
verified. The parent uses both children.
The general coordinate signature remains open pending the cited Brändén–Huh
result or an independent proof; no directional conclusion is assumed here.
-/

namespace CountingMatroid.Analysis.RankWeightCoordinateLorentzian

open scoped BigOperators
open LorentzianDirectionalSignature



/-- PAPER: main.tex:334-348
The coordinate certificate for the homogenized matroid rank-weight polynomial.
This is the matroid-specific input, separated from the general theorem about
nonnegative directional derivatives.
BORROWED: Brändén–Huh, Lorentzian polynomials (2020), Theorem 4.10
supplies Lorentzianity, hence its coordinate quadratic signatures. The support
exchange component is verified directly from the subset exponents. -/
theorem rank_weight_coordinate_lorentzian {α : Type} [Fintype α] [DecidableEq α]
    (N : Matroid α) (hfull : N.E = Set.univ)
    (q : ℚ) (hq : 0 < q) (hqone : q ≤ 1) :
    CoordinateLorentzian
      (∑ A : Finset α,
        MvPolynomial.C ((q ^ (N.eRk (A : Set α)).toNat)⁻¹) *
          MvPolynomial.X none ^ (Fintype.card α - A.card) *
            ∏ a ∈ A, MvPolynomial.X (some a))
      (Fintype.card α) := by
  classical
  obtain ⟨hhom, hcoeff⟩ := rank_weight_basic_invariants N q hq
  exact ⟨hhom, hcoeff,
    RankWeightSupportExchange.rank_weight_support_exchange N q hq,
    RankWeightCoordinateSignature.rank_weight_coordinate_signature N hfull q hq hqone⟩

end CountingMatroid.Analysis.RankWeightCoordinateLorentzian

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · partial · proved subset support exchange in RankWeightSupportExchange and assembled the parent certificate through that theorem and the independent RankWeightCoordinateSignature child. Only the general coordinate Hessian bound remains open; the binary and vacuous proofs are preserved in that child.
* 2026-10-09 · blocked · preserved basic invariants and the binary signature proof; discharged the vacuous signature branch below ground size two. Statement-shape searches in pinned Mathlib, Arlib and the project found no independent Brändén–Huh rank-polynomial theorem or coordinate-certificate bridge. The direct generic hyperplane application timed out during definitional equality; the available binary theorem requires ground size two. Proposed the unchanged cited base certificate as prior input, without adding assumptions or child proof debt.
-/

end

section


set_option autoImplicit false

/-!
The original-variable mixed-derivative prerequisite for the rank-weight
signature theorem. Linear substitution and scalar closure are proved in the
parent's other support modules. The empty direction list is handled by
the two-element rank-weight calculation, and an identically zero direction
anywhere in the list gives the zero quadratic form. The remaining case,
where the list is nonempty and every direction is nonzero, now uses two
separate prerequisites: the matroid-specific coordinate Lorentzian certificate
in `RankWeightCoordinateLorentzian`, and the general nonnegative directional
signature consequence in `LorentzianDirectionalSignature`. Both support files
were released through a compiler-validated scheduler handoff; this module
does not supply their full proofs. Their basic degree/coefficient facts and
degree-two closure case are proved. The passage from a signature bound to a
hyperplane is proved by Mathlib diagonalization in
`QuadraticSignatureHyperplane`. The target proof contains no local hole,
but its full proof depends on both prerequisites; the pinned libraries contain
no applicable Lorentzian API.
-/

namespace CountingMatroid.Analysis.MixedDirectionalRankWeightSignature

open scoped BigOperators
open QuadraticNonpositiveHyperplane

/-- INTERNAL: A zero direction anywhere in the mixed-derivative list
annihilates the polynomial, and all subsequent derivatives preserve zero.
TEXLINE: main.tex:340-343 -/
theorem mixed_derivatives_eq_zero_of_zero_mem {σ : Type} [Fintype σ]
    (ds : List (σ → ℚ)) (f : MvPolynomial σ ℚ)
    (hz : ∃ d ∈ ds, ∀ s, d s = 0) :
    ds.foldr (fun d f => ∑ s, MvPolynomial.C (d s) * MvPolynomial.pderiv s f) f = 0 := by
  induction ds with
  | nil => simp only [List.not_mem_nil, false_and, exists_false] at hz
  | cons d ds ih =>
    obtain ⟨e, he, hezero⟩ := hz
    rcases List.mem_cons.mp he with rfl | he
    · simp only [List.foldr_cons, hezero, map_zero, zero_mul, Finset.sum_const_zero]
    · rw [List.foldr_cons, ih ⟨e, he, hezero⟩]
      simp only [map_zero, mul_zero, Finset.sum_const_zero]



end CountingMatroid.Analysis.MixedDirectionalRankWeightSignature

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · validated parallel handoff · request agent5-coordinate-lorentzian-20261009-1 accepted at semantic-use stage; LorentzianDirectionalSignature and RankWeightCoordinateLorentzian transferred to scheduler ownership. The unchanged target has a complete proof body using both children; the mathematical proof debt is explicitly retained in their open base-certificate and directional-closure declarations.
* 2026-10-09 · decomposed · introduced the coordinate Lorentzian certificate and separated the matroid-specific certificate from general nonnegative directional closure. Proved the basic homogeneous-degree/coefficient invariants and the general degree-two closure case. The target uses both children; support exchange, higher-degree coordinate signatures, and general directional closure remain open for live OPEN handoff. No Prior field or assumption was added.
* 2026-10-09 · partial · proved QuadraticSignatureHyperplane.hasNonpositiveHyperplane_of_sigPos_le_one using Mathlib's weighted-square diagonalization and signature count; the nonempty branch now uses it. The remaining single hole is the at-most-one-positive Hessian signature bound from the cited Lorentzian base and closure input, absent from the pinned libraries. No assumption or open child lemma was added.
* 2026-10-09 · blocked · independently verified the borrowed-library blocker with symlink-following searches of all pinned Lean sources, including matroid/polynomial statement shapes and quadratic-signature APIs; no applicable base or closure input was found. Preserved every proof and the exact target, adding only diagnostic evidence; no new lemma, assumption, proof debt or import.
* 2026-10-09 · partial · proved mixed_derivatives_eq_zero_of_zero_mem and used it to close every list containing an identically zero direction, preserving the empty-list proof. Statement-shape searches including polynomial stability, complete log-concavity, quadratic signature and Arlib's local-to-global/PSD APIs found no applicable borrowed input. The nonempty all-nonzero case remains the same single proof hole; no assumption, child proof debt or import was added.
* 2026-10-09 · blocked · proved the identically zero head-direction branch; searched pinned Mathlib and Arlib by Lorentzian/log-concave closure, matroid polynomial Hessian and positive signature without finding the cited input. Stdin probes verified the tail-length and binary-cardinality mismatches. Proposed this unchanged Brändén–Huh consequence as prior input; no new helper, assumption or import was introduced.
* 2026-10-09 · open · stated the exact original-variable mixed-directional prerequisite and proved its empty-direction branch using BinaryRankWeightSignature; direct list induction cannot use its quadratic induction hypothesis on the cubic tail.
-/

end
set_option autoImplicit false

/-!
The original-variable mixed-derivative prerequisite for the rank-weight
signature theorem. Linear substitution and scalar closure are proved in the
parent's other support modules. The empty direction list is handled by
the two-element rank-weight calculation, and an identically zero direction
anywhere in the list gives the zero quadratic form. The remaining case,
where the list is nonempty and every direction is nonzero, now uses two
separate prerequisites: the matroid-specific coordinate Lorentzian certificate
in `RankWeightCoordinateLorentzian`, and the general nonnegative directional
signature consequence in `LorentzianDirectionalSignature`. Both support files
were released through a compiler-validated scheduler handoff; this module
does not supply their full proofs. Their basic degree/coefficient facts and
degree-two closure case are proved. The passage from a signature bound to a
hyperplane is proved by Mathlib diagonalization in
`QuadraticSignatureHyperplane`. The target proof contains no local hole,
but its full proof depends on both prerequisites; the pinned libraries contain
no applicable Lorentzian API.
-/

namespace CountingMatroid.Analysis.MixedDirectionalRankWeightSignature
end CountingMatroid.Analysis.MixedDirectionalRankWeightSignature
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.MixedDirectionalRankWeightSignature

open scoped BigOperators
open QuadraticNonpositiveHyperplane

/-- PAPER: main.tex:334-348
The original-variable hyperplane consequence of the cited Lorentzian base
and closure results,
for the common matroid polynomial after exactly ground-size minus two
nonnegative directional derivatives. The fold is the parent's proved normal
form, with the last derivative at the head of the list.
BORROWED: Bränden–Huh, Lorentzian polynomials (2020), Theorems 4.10,
2.10 and Corollary 2.11 supply the Lorentzian base and closure input. -/
theorem solution {α : Type}
    [Fintype α] [DecidableEq α] (N : Matroid α) (hfull : N.E = Set.univ)
    (q : ℚ) (hq : 0 < q) (hqone : q ≤ 1)
    (ds : List (Option α → ℚ))
    (hds : ∀ d ∈ ds, ∀ s, 0 ≤ d s)
    (hlength : ds.length + 2 = Fintype.card α) :
    let p : MvPolynomial (Option α) ℚ := ∑ A : Finset α,
      MvPolynomial.C ((q ^ (N.eRk (A : Set α)).toNat)⁻¹) *
        MvPolynomial.X none ^ (Fintype.card α - A.card) *
          ∏ a ∈ A, MvPolynomial.X (some a)
    let g := ds.foldr (fun d f => ∑ s, MvPolynomial.C (d s) * MvPolynomial.pderiv s f) p
    HasNonpositiveHyperplane (Matrix.toQuadraticForm' (fun i j =>
      ((MvPolynomial.constantCoeff (MvPolynomial.pderiv i (MvPolynomial.pderiv j g)) : ℚ) : ℝ))) := by
  by_cases hz : ∃ d ∈ ds, ∀ s, d s = 0
  · dsimp only
    rw [mixed_derivatives_eq_zero_of_zero_mem ds _ hz]
    simp only [map_zero, Rat.cast_zero]
    refine ⟨0, ?_⟩
    intro v hv
    change Matrix.toLinearMap₂' ℝ (0 : Matrix (Option α) (Option α) ℝ) v v ≤ 0
    rw [map_zero]
    simp
  · cases ds with
    | nil =>
      exact BinaryRankWeightSignature.binary_tutte_nonpositive_hyperplane
        N q hq hqone (by simpa using hlength.symm)
    | cons d ds =>
      apply QuadraticSignatureHyperplane.hasNonpositiveHyperplane_of_sigPos_le_one
      -- The missing published inputs are now separate child obligations.
      -- The following comments preserve the pre-decomposition proof evidence.
      -- The linear-algebra implication is now proved: diagonalization
      -- deletes the sole positive square and transports its kernel back.
      -- The remaining goal is exactly sigPos of the displayed Hessian ≤ 1;
      -- it still needs the cited matroid-polynomial base/closure input.
      -- BLOCKER: library name not found. Statement-shape searches of pinned
      -- Mathlib and Arlib found no rank-weight polynomial Hessian bound,
      -- Lorentzian/complete-log-concavity invariant, or polynomial-stability
      -- closure supplying the common nonpositive hyperplane. Mathlib's
      -- quadratic signature API bounds dimension given a nonpositive subspace;
      -- it does not establish that subspace for these matroid coefficients.
      -- Arlib's local-to-global variance identities and PSD-order closure
      -- likewise do not provide the required matroid-polynomial input.
      -- Rechecked with hidden/ignored files included and package symlinks
      -- followed: Mathlib's matroid sources contain no Polynomial or
      -- MvPolynomial API; Arlib has no Matroid, MvPolynomial, pderiv or
      -- eRk declaration. No Lorentzian, complete-log-concavity, real-stable
      -- or hyperbolic-polynomial result was found in either library.
      -- Precisely missing are: Lorentzianity of the displayed T_{q,N},
      -- preservation by the nonnegative directional fold, and the quadratic
      -- Hessian implication giving HasNonpositiveHyperplane. The available
      -- QuadraticForm.sigPos_add_finrank_le_of_nonpos instead requires the
      -- nonpositive subspace as a hypothesis; it cannot supply this witness.
      -- The cited input is main.tex:334-348, BH2020 Theorems 4.10, 2.10
      -- and Corollary 2.11. Propose this exact consequence as prior input;
      -- no field of Prior has been added or assumed here.
      -- A stdin induction attempt failed on ds.length + 2 = |α|:
      -- this branch instead has ds.length + 3 = |α|, so the tail is cubic.
      -- Focused arithmetic probes also prove |α| ≠ 2 here, ruling out
      -- binary_tutte_nonpositive_hyperplane. Separate hyperplanes for the
      -- coordinate derivative Hessians cannot be added into a shared one.
      -- RankWeightQuadraticSignature imports and uses this theorem, so its
      -- general signature declaration cannot be imported as a proof of it.
      exact LorentzianDirectionalSignature.directional_hessian_sigPos_le_one _ _
        (RankWeightCoordinateLorentzian.rank_weight_coordinate_lorentzian
          N hfull q hq hqone) (d :: ds) hds hlength
