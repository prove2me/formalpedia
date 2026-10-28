-- Prove2me | solution 1 for CountingMatroid.Analysis.ConditionalDefectCoefficientBounds.conditional_defect_coefficient_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:20:21.139388+00:00
-- url     : https://prove2.me/submissions/4a290ab9-e2a4-4a4b-b2b8-6749613d7e40

import Definitions.Def_CountingMatroidSupport_Computation_Charged
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension2
import Definitions.Def_CountingMatroidSupport_Computation_Cost
import Definitions.Def_CountingMatroidSupport_Computation_Cost_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Dict
import Definitions.Def_CountingMatroidSupport_Computation_Heap
import Definitions.Def_CountingMatroidSupport_Computation_Machine
import Definitions.Def_CountingMatroidSupport_Computation_Machine_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Num
import Definitions.Def_CountingMatroidSupport_Computation_Queue
import Definitions.Def_CountingMatroidSupport_Computation_Rand
import Definitions.Def_CountingMatroidSupport_Computation_Roster
import Definitions.Def_CountingMatroidSupport_Computation_Slot
import Definitions.Def_CountingMatroidSupport_Computation_Space
import Definitions.Def_CountingMatroidSupport_Computation_Std
import Definitions.Def_CountingMatroidSupport_MarkovChains_Chains_Metropolis
import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_Dirichlet
import Definitions.Def_CountingMatroidSupport_Probability_Bilinear
import Definitions.Def_CountingMatroidSupport_Probability_FinDist
import Definitions.Def_CountingMatroidSupport_Probability_FinDistFunctional
import Definitions.Def_CountingMatroid_Analysis_AnnealingPartitionDrift
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhase
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhaseHistory
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhaseWork
import Definitions.Def_CountingMatroid_Analysis_ConditionalDefectCoefficients
import Definitions.Def_CountingMatroid_Analysis_ConditionalDefectExtractionCoefficients
import Definitions.Def_CountingMatroid_Analysis_ConditionalDefectQuadratics
import Definitions.Def_CountingMatroid_Analysis_ConditionalSelectedStateSum
import Definitions.Def_CountingMatroid_Analysis_CubicTensorContraction
import Definitions.Def_CountingMatroid_Analysis_DefectPartitionPositive
import Definitions.Def_CountingMatroid_Analysis_DefectPartitionQuadraticConstruction
import Definitions.Def_CountingMatroid_Analysis_EmpiricalPhaseCertificate
import Definitions.Def_CountingMatroid_Analysis_EstimateMedianResource
import Definitions.Def_CountingMatroid_Analysis_ExchangeFlowEnergy
import Definitions.Def_CountingMatroid_Analysis_FinishPhaseEmpiricalUpdate
import Definitions.Def_CountingMatroid_Analysis_FinishPhaseWork
import Definitions.Def_CountingMatroid_Analysis_FirstPhaseFailure
import Definitions.Def_CountingMatroid_Analysis_IdealExchangeChain
import Definitions.Def_CountingMatroid_Analysis_InitialMultipliersGood
import Definitions.Def_CountingMatroid_Analysis_LorentzianDirectionalSignature
import Definitions.Def_CountingMatroid_Analysis_ObservableProjection
import Definitions.Def_CountingMatroid_Analysis_ObservableVarianceDecomposition
import Definitions.Def_CountingMatroid_Analysis_ObservePhaseWork
import Definitions.Def_CountingMatroid_Analysis_OmittedRankWeightPolynomial
import Definitions.Def_CountingMatroid_Analysis_OmittedSlotQuadratic
import Definitions.Def_CountingMatroid_Analysis_OmittedTutteNormalization
import Definitions.Def_CountingMatroid_Analysis_PhaseChainWork
import Definitions.Def_CountingMatroid_Analysis_PhaseMeanCertificate
import Definitions.Def_CountingMatroid_Analysis_PhaseResourcePrimitives
import Definitions.Def_CountingMatroid_Analysis_QuadraticNonpositiveHyperplane
import Definitions.Def_CountingMatroid_Analysis_RankWeightQuadraticSignature
import Definitions.Def_CountingMatroid_Analysis_RankWeightSupportExchange
import Definitions.Def_CountingMatroid_Analysis_RationalHeight
import Definitions.Def_CountingMatroid_Analysis_RelativeObservationBounds
import Definitions.Def_CountingMatroid_Analysis_ScheduleConfidence
import Definitions.Def_CountingMatroid_Analysis_ScheduleOpeningCost
import Definitions.Def_CountingMatroid_Analysis_ScheduleThermalSetupCost
import Definitions.Def_CountingMatroid_Analysis_SquarefreeCoordinateHessian
import Definitions.Def_CountingMatroid_Analysis_StationaryMeanIdentities
import Definitions.Def_CountingMatroid_Analysis_ThreePairSignatureSchur
import Definitions.Def_CountingMatroid_Analysis_TransversalClassPartition
import Definitions.Def_CountingMatroid_Analysis_TransversalEventMean
import Definitions.Def_CountingMatroid_Analysis_TransversalPartition
import Definitions.Def_CountingMatroid_Analysis_TransversalProjection
import Definitions.Def_CountingMatroid_Analysis_TwoPairSignatureBound
import Definitions.Def_CountingMatroid_Interface_Pseudocode
import Definitions.Def_CountingMatroid_Interface_Pseudocode_Extension1
import Definitions.Def_CountingMatroid_Model_Operations
import Definitions.Def_CountingMatroid_Model_Prelude
import Definitions.Def_CountingMatroid_Model_Program
import Definitions.Def_CountingMatroid_Model_Run
import Definitions.Def_CountingMatroid_Model_Subroutines
import Lean
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Combinatorics.Matroid.Sum
import Mathlib.Data.BitVec
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finsupp.Indicator
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Induction
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sort
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.Count
import Mathlib.Data.Nat.Log
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Data.Set.Finite.List
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Signature
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Instances.Real.Lemmas
import Theorems.Thm_CountingMatroid_Analysis_ConditionalDefectCoefficients_defect_total_pos
import Theorems.Thm_CountingMatroid_Analysis_ConditionalDefectCoefficients_transversal_total_pos
import Theorems.Thm_CountingMatroid_Analysis_ConditionalDefectExtractionCoefficients_conditioned_pair_coefficient
import Theorems.Thm_CountingMatroid_Analysis_ConditionalDefectExtractionCoefficients_conditioned_triple_coefficient
import Theorems.Thm_CountingMatroid_Analysis_ConditionalDefectQuadratics_conditioned_pair_quadratic
import Theorems.Thm_CountingMatroid_Analysis_ConditionalDefectQuadratics_conditioned_triple_quadratic
import Theorems.Thm_CountingMatroid_Analysis_ConditionalOperationalCoefficients_conditional_operational_coefficients
import Theorems.Thm_CountingMatroid_Analysis_RankWeightQuadraticSignature_branden_huh_quadratic_signature
import Theorems.Thm_CountingMatroid_Analysis_ThreePairSignatureSchur_three_pair_signature_schur
import Theorems.Thm_CountingMatroid_Analysis_TwoPairSignatureBound_two_pair_signature_bound

namespace CountingMatroid.Analysis.DefectPartitionTriangle
end CountingMatroid.Analysis.DefectPartitionTriangle
namespace CountingMatroid.Analysis.DefectPartitionQuadraticExtraction
end CountingMatroid.Analysis.DefectPartitionQuadraticExtraction
namespace CountingMatroid.Analysis.ConditionalOperationalCoefficients
end CountingMatroid.Analysis.ConditionalOperationalCoefficients
namespace CountingMatroid.Analysis.SignatureOrthogonalNonpositive
end CountingMatroid.Analysis.SignatureOrthogonalNonpositive
namespace CountingMatroid.Analysis.ConditionalOccupancyCoefficients
end CountingMatroid.Analysis.ConditionalOccupancyCoefficients
namespace CountingMatroid.Analysis.TwoLabelDerivativeNilpotence
end CountingMatroid.Analysis.TwoLabelDerivativeNilpotence
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
namespace CountingMatroid.Analysis.LinearSubstitutionHessian
end CountingMatroid.Analysis.LinearSubstitutionHessian
namespace CountingMatroid.Analysis.LinearPolynomialChainRule
end CountingMatroid.Analysis.LinearPolynomialChainRule
namespace CountingMatroid.Analysis.GreedyRankCorrect
end CountingMatroid.Analysis.GreedyRankCorrect
namespace Arlib
end Arlib
namespace CountingMatroid.Interface
end CountingMatroid.Interface
namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace CountingMatroid.Analysis.TransversalRankBridge
end CountingMatroid.Analysis.TransversalRankBridge
namespace CountingMatroid.Analysis.PairedRankValue
end CountingMatroid.Analysis.PairedRankValue
namespace CountingMatroid.Analysis.TypeMassLowerBounds
end CountingMatroid.Analysis.TypeMassLowerBounds
namespace CountingMatroid.Analysis.BoundedRunResourceEnvelope
end CountingMatroid.Analysis.BoundedRunResourceEnvelope
namespace CountingMatroid.Analysis.BoundedRunOtherSteps
end CountingMatroid.Analysis.BoundedRunOtherSteps
namespace CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
end CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
namespace CountingMatroid.Analysis.LeastHalvingsCost
end CountingMatroid.Analysis.LeastHalvingsCost
namespace CountingMatroid.Analysis
end CountingMatroid.Analysis
namespace CountingMatroid.Analysis.RestartPhaseWork
end CountingMatroid.Analysis.RestartPhaseWork
namespace CountingMatroid.Analysis.BoundedRunPhase
end CountingMatroid.Analysis.BoundedRunPhase
namespace CountingMatroid.Analysis.FinishPhaseWeightsSize
end CountingMatroid.Analysis.FinishPhaseWeightsSize
namespace CountingMatroid.Analysis.BoundedRunOracleCalls
end CountingMatroid.Analysis.BoundedRunOracleCalls
namespace CountingMatroid.Analysis.ResourceBound
end CountingMatroid.Analysis.ResourceBound
namespace CountingMatroid.Analysis.ConditionalDefectCoefficientBounds
end CountingMatroid.Analysis.ConditionalDefectCoefficientBounds
section


set_option autoImplicit false

/-!
The precise external signature input, separate from the operational rank
correspondence and coefficient extraction proved in the counting paper.
`Descendant` records only partial derivatives, nonnegative linear
substitutions, and nonnegative scalar multiplication. The signature uses
Mathlib's maximum dimension of a positive definite subspace over the reals.
The empty- and singleton-ground signature cases are proved, using the
homogeneous-degree invariant of every descendant. The two-element ground
case is proved by rank submodularity and a two-square calculation, with
the resulting hyperplane transported through every allowed substitution.
The signature case with at most one output variable follows from the ambient
dimension bound. The remaining
Bränden–Huh input is the unresolved borrowed mixed-derivative prerequisite
in `MixedDirectionalRankWeightSignature`. The exact normal
form of a descendant is proved: nonnegative directional derivatives in the
original variables, followed by one nonnegative linear substitution and a
nonnegative scalar. A nonzero quadratic uses exactly ground-set size minus
two derivatives. The unresolved signature bound is applied to this normal
form. A proved nonpositive-hyperplane invariant transports the Hessian
through the final substitution and scaling and recovers the exact orthogonal
kernel used by the signature bound. Only its establishment for the original
mixed directional derivative on ground sets of size at least three remains
open in that support module; no Lorentzian assumption has been introduced.
-/

namespace CountingMatroid.Analysis.RankWeightQuadraticSignature

open scoped BigOperators









/-- INTERNAL: Compute a Hessian entry directly from a degree-two coefficient;
the repeated-variable coefficient has multiplicity two.
TEXLINE: main.tex:408-417 -/
theorem hessian_coefficient {τ : Type} [DecidableEq τ]
    (g : MvPolynomial τ ℚ) (s t : τ) :
    hessian g s t =
      ((g.coeff (Finsupp.single s 1 + Finsupp.single t 1) *
        (if s = t then 2 else 1) : ℚ) : ℝ) := by
  classical
  unfold hessian
  rw [MvPolynomial.constantCoeff_eq, MvPolynomial.coeff_pderiv,
    MvPolynomial.coeff_pderiv]
  by_cases h : s = t
  · subst t
    norm_num
  · simp [h, Finsupp.single_apply, Ne.symm h]



























end CountingMatroid.Analysis.RankWeightQuadraticSignature

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · handoff-ready · after the live scheduler opened capacity, isolated the sole remaining original-variable invariant in MixedDirectionalRankWeightSignature and proved the fold identity connecting it to the parent. All other children are proved; the parent uses the independent prerequisite and contains no remaining proof hole of its own. The prerequisite still has the mixed-directional compatibility gap, so this is a proof boundary, not a completed Bränden–Huh proof.
* 2026-10-09 · partial · proved Hessian congruence under linear substitution and scalar scaling, and the nonpositive-hyperplane invariant with its pullback, scaling, signature and positive-vector orthogonal-kernel consequences. Proved the two-element Tutte quadratic by the exact rank-weight pair bound and a two-square identity, so the parent closes every descendant on ground sets of size at most two. Its single remaining gap is establishment of the invariant for |α|≥3 after exactly |α|-2 nonnegative directional derivatives; all subsequent transport is proved. No new assumption or open child was introduced.
* 2026-10-09 · partial · proved the linear polynomial chain rule and substitution composition in LinearPolynomialChainRule, then proved finite intermediate variables, the exact directional normal form, and its homogeneous degree. The parent uses this representation and proves that its direction list has length |α|-2 and its scalar is positive. The original nonpositive-kernel gap now concerns this normalized expression. A stdin application of eRk_submod failed by statement shape; separate checked stdin examples show that adding two signature-one forms can produce signature two. The unresolved cited input is compatibility of mixed nonnegative directional derivatives of the common matroid polynomial, not the algebraic normalization. No assumption or new open helper was introduced.
* 2026-10-09 · partial · proved the at-most-one-output-variable branch using sigPos_le_finrank and Module.finrank_pi; preserved all earlier homogeneous-degree, coefficient-cone and small-ground proofs. Current statement-shape searches found no matroid-polynomial, Lorentzian closure or substitute spectral declaration supplying nonpositivity on the positive-vector orthogonal complement. The remaining cited Bränden–Huh input stays open in its original theorem, without new helpers or assumptions.
* 2026-10-09 · blocked · preserved the proved empty-ground branch; searched project, pinned Mathlib and Arlib for Lorentzian rank-weight base, closure and quadratic signature results without finding an applicable declaration. A stdin application of descendant_constant to the nonempty branch fails because its initial polynomial must be constant. Proposed the unchanged cited Bränden–Huh consequence as prior input; introduced no helper or assumption.
-/

end

section


set_option autoImplicit false

/-!
The concrete selected-element quadratic used in the three-pair inequality.
It is constructed from the homogenized Tutte polynomial by the paper's
actual derivative and substitution sequence. Its membership in the allowed
closure operations is proved separately from its operational coefficients.
Its last diagonal Hessian entry is proved to vanish directly from squarefree
label exponents, without any operational coefficient identity.
The remaining coefficient identities need the paired-rank correspondence
and extraction calculation; it does not assume a signature theorem. The
existing paired-rank correspondence and extraction-calculus lemmas live in
modules that import this module. Reusing them here requires separating the
construction declarations above the operational extraction theorem from
that theorem, so those dependencies no longer import their consumer.
-/

namespace CountingMatroid.Analysis.DefectPartitionQuadraticExtraction

open CountingMatroid.Model
open CountingMatroid.Analysis.RankWeightQuadraticSignature
open CountingMatroid.Analysis.ThreePairSignatureSchur
open CountingMatroid.Analysis.TwoLabelDerivativeNilpotence



/-- INTERNAL: The paired matroid has exactly the supplied paired ground.
TEXLINE: main.tex:262-272 -/
theorem paired_matroid_full_ground {n : ℕ} (M₁ M₂ : Matroid (Fin n))
    (hfull : FullGround M₁ M₂) : (pairedMatroid M₁ M₂).E = Set.univ := by
  ext e
  rcases e with ⟨i, b⟩
  cases b <;> simp [pairedMatroid, hfull.1, hfull.2]























end CountingMatroid.Analysis.DefectPartitionQuadraticExtraction

end

section


set_option autoImplicit false

/-!
The unconditional three-pair coefficient inequality used to bound the cost
of the defect transport. The q=1 case, the numerical Schur-complement
step, and the real-signature-to-rational-Schur step are proved. The parent
now uses a concrete homogeneous quadratic constructed by the paper's
derivatives and substitutions. Its operational coefficient identity and
the cited Bränden–Huh signature input remain open in their support files.
-/

namespace CountingMatroid.Analysis.DefectPartitionTriangle

open CountingMatroid.Model CountingMatroid.Program

/-- INTERNAL: The numerical three-pair Schur-complement step, with its
zero final diagonal and all factors in the operational rational field.
TEXLINE: main.tex:430-449 -/
theorem three_pair_schur_bound (a c d e z : ℚ)
    (ha : 0 ≤ a) (hc : 0 < c) (he : 0 < e) (hz : 0 < z)
    (hschur : ∀ x y : ℚ,
      2 * c * (2 * a * x ^ 2 + 4 * d * x * y) ≤
        (z * x + 2 * e * y) ^ 2) : c * d ≤ z * e := by
  have h := hschur (2 * e) z
  have hdiag : 0 ≤ 2 * c * (2 * a * (2 * e) ^ 2) :=
    mul_nonneg (by positivity) (mul_nonneg (by positivity) (sq_nonneg _))
  have hdiff : 0 ≤ (z * e - c * d) * (16 * z * e) := by
    nlinarith [hdiag]
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_left hdiff (by positivity))



end CountingMatroid.Analysis.DefectPartitionTriangle

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · decomposed · connected the parent to the concrete Tutte-polynomial derivative/substitution construction; proved its homogeneous degree and the real-signature-to-rational-Schur implication. The two remaining prerequisites are the operational Hessian coefficient identity and the explicitly cited Bränden–Huh quadratic signature theorem.
* 2026-10-09 · partial · proved the q=1 branch, positivity of all needed operational totals, and `three_pair_schur_bound`; the sole remaining local gap is the explicit extracted-Hessian Schur-complement bound for 0<q<1. Direct finite-sum positivity does not compare the products; pinned Mathlib and Arlib contain no Lorentzian rank-weight signature or closure theorem.
-/

end
set_option autoImplicit false

/-!
The two coefficient inequalities for partial transversal assignments.
The coefficients are the concrete finite operational-rank sums defined in
`ConditionalDefectCoefficients`, rather than unspecified polynomial data.
The actual conditioned descendants and their degrees are constructed in
`ConditionalDefectQuadratics`. Their exact ordinary-pair extraction and
coordinate-restriction coefficient calculations, selected-label derivatives,
and exact q^n/n! normalization are proved in
`ConditionalDefectExtractionCoefficients` and used below. The determinant
and Schur consequences are connected to those descendants via the existing
Bränden–Huh signature declaration. The exact normalization and operational
rank-weight state sums are proved in `ConditionalSelectedStateSum`.
`ConditionalOperationalCoefficients` carries the remaining independent
occupancy-to-classification identity used here. The target has no local
proof gap; completion depends on that coefficient bridge and the existing
signature input. No extra theorem hypothesis is introduced.
-/

namespace CountingMatroid.Analysis.ConditionalDefectCoefficientBounds
end CountingMatroid.Analysis.ConditionalDefectCoefficientBounds
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.ConditionalDefectCoefficientBounds

open CountingMatroid.Model
open CountingMatroid.Analysis.ConditionalDefectCoefficients
open CountingMatroid.Analysis.ConditionalDefectQuadratics
open CountingMatroid.Analysis.ConditionalDefectExtractionCoefficients
open CountingMatroid.Analysis.RankWeightQuadraticSignature
open CountingMatroid.Analysis.DefectPartitionQuadraticExtraction
open CountingMatroid.Analysis.TwoPairSignatureBound
open CountingMatroid.Analysis.ThreePairSignatureSchur

/-- PAPER: main.tex:397-449
Both defect inequalities hold at every conditioning node, with all displayed
defect indices unassigned and pairwise distinct. -/
theorem solution (n r : ℕ)
    (M₁ M₂ : Matroid (Fin n)) (o₁ o₂ : IndependenceOracle n) (q : ℚ)
    (hfull : FullGround M₁ M₂) (hr : CommonRank r M₁ M₂)
    (h₁ : ExactOracle M₁ o₁) (h₂ : ExactOracle M₂ o₂)
    (hq : 0 < q) (hqone : q ≤ 1) (σ : Assignment n) :
    (∀ (i j : Fin n) (hij : i ≠ j), σ i = none → σ j = none →
      4 * defectTotal r o₁ o₂ q σ ⟨i, j, hij⟩ *
        defectTotal r o₁ o₂ q σ ⟨j, i, hij.symm⟩ ≤
          transversalTotal r o₁ o₂ q σ ^ 2) ∧
    (∀ (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k),
      σ i = none → σ j = none → σ k = none →
      defectTotal r o₁ o₂ q σ ⟨i, j, hij⟩ *
        defectTotal r o₁ o₂ q σ ⟨j, k, hjk⟩ ≤
          transversalTotal r o₁ o₂ q σ * defectTotal r o₁ o₂ q σ ⟨i, k, hik⟩) := by
  classical
  let P := conditionedPairPolynomial M₁ M₂ q σ
  let D := defectTotal r o₁ o₂ q σ
  let Z := transversalTotal r o₁ o₂ q σ
  have hz : 0 < Z := transversal_total_pos r o₁ o₂ q hq σ
  have hc (index : DefectIndex n) (he : σ index.emptyPair = none)
      (hf : σ index.fullPair = none) : 0 < D index :=
    defect_total_pos r o₁ o₂ q hq σ index he hf
  -- The coefficient bridge uses the proved operational state-sum
  -- representation; the determinant and Schur arguments below use its
  -- exact pair and triple entries.
  have hcoeff :
      (∀ (i j : Fin n) (hij : i ≠ j), σ i = none → σ j = none →
        ∀ s t : Fin 2,
          ((P.coeff ((Finsupp.single s 1 + Finsupp.single t 1).mapDomain
              (![i, j] : Fin 2 → Fin n) + ordinaryExponent σ {i, j}) *
            (if s = t then 2 else 1) : ℚ) : ℝ) =
          twoPairMatrix (D ⟨j, i, hij.symm⟩) (D ⟨i, j, hij⟩) Z s t) ∧
      (∀ (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k),
        σ i = none → σ j = none → σ k = none → ∀ s t : Fin 3,
          ((P.coeff ((Finsupp.single s 1 + Finsupp.single t 1).mapDomain
              (![i, j, k] : Fin 3 → Fin n) + Finsupp.single k 1 +
              ordinaryExponent σ {i, j, k}) *
            ((Finsupp.single s 1 + Finsupp.single t 1 : Fin 3 →₀ ℕ) 2 + 1) *
            (if s = t then 2 else 1) : ℚ) : ℝ) =
          threePairMatrix (D ⟨j, i, hij.symm⟩) (D ⟨i, j, hij⟩)
            (D ⟨j, k, hjk⟩) (D ⟨i, k, hik⟩) Z s t) := by
    exact CountingMatroid.Analysis.ConditionalOperationalCoefficients.conditional_operational_coefficients
      n r M₁ M₂ o₁ o₂ q hfull hr h₁ h₂ hq σ

  constructor
  · intro i j hij hi hj
    have hquad := conditioned_pair_quadratic M₁ M₂ q hq σ i j hij hi hj
    have hsig := branden_huh_quadratic_signature (pairedMatroid M₁ M₂)
      (paired_matroid_full_ground M₁ M₂ hfull) q hq hqone
      (conditionedPairQuadratic M₁ M₂ q σ i j) hquad.1 hquad.2
    have hmatrix : hessian (conditionedPairQuadratic M₁ M₂ q σ i j) =
        twoPairMatrix (D ⟨j, i, hij.symm⟩) (D ⟨i, j, hij⟩) Z := by
      ext s t
      rw [hessian_coefficient, conditioned_pair_coefficient M₁ M₂ q σ i j hij]
      exact hcoeff.1 i j hij hi hj s t
    rw [hmatrix] at hsig
    exact two_pair_signature_bound _ _ _ (hc _ hj hi) hsig
  · intro i j k hij hjk hik hi hj hk
    have hquad := conditioned_triple_quadratic M₁ M₂ q hq σ i j k hij hjk hik hi hj hk
    have hsig := branden_huh_quadratic_signature (pairedMatroid M₁ M₂)
      (paired_matroid_full_ground M₁ M₂ hfull) q hq hqone
      (conditionedTripleQuadratic M₁ M₂ q σ i j k) hquad.1 hquad.2
    have hmatrix : hessian (conditionedTripleQuadratic M₁ M₂ q σ i j k) =
        threePairMatrix (D ⟨j, i, hij.symm⟩) (D ⟨i, j, hij⟩)
          (D ⟨j, k, hjk⟩) (D ⟨i, k, hik⟩) Z := by
      ext s t
      rw [hessian_coefficient,
        conditioned_triple_coefficient M₁ M₂ q σ i j k hij hjk hik]
      exact hcoeff.2 i j k hij hjk hik hi hj hk s t
    rw [hmatrix] at hsig
    have hschur := three_pair_signature_schur _ _ _ _ _ (hc _ hi hj) hsig
    exact CountingMatroid.Analysis.DefectPartitionTriangle.three_pair_schur_bound
      _ _ _ _ _ (hc _ hj hi).le (hc _ hi hj) (hc _ hi hk) hz hschur
