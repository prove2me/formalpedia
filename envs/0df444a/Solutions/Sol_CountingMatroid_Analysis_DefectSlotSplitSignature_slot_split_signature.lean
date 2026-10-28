-- Prove2me | solution 1 for CountingMatroid.Analysis.DefectSlotSplitSignature.slot_split_signature
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:19:24.198996+00:00
-- url     : https://prove2.me/submissions/39988227-e2c3-41cc-b5e5-3ef91b620b4a

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
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhase
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhaseHistory
import Definitions.Def_CountingMatroid_Analysis_ConditionalDefectCoefficients
import Definitions.Def_CountingMatroid_Analysis_ConditionalDefectExtractionCoefficients
import Definitions.Def_CountingMatroid_Analysis_ConditionalDefectQuadratics
import Definitions.Def_CountingMatroid_Analysis_CubicTensorContraction
import Definitions.Def_CountingMatroid_Analysis_DefectPartitionQuadraticConstruction
import Definitions.Def_CountingMatroid_Analysis_DefectSlotSplitSignature
import Definitions.Def_CountingMatroid_Analysis_FirstPhaseFailure
import Definitions.Def_CountingMatroid_Analysis_InitialMultipliersGood
import Definitions.Def_CountingMatroid_Analysis_LorentzianDirectionalSignature
import Definitions.Def_CountingMatroid_Analysis_OmittedRankWeightPolynomial
import Definitions.Def_CountingMatroid_Analysis_OmittedSlotCoefficientFormula
import Definitions.Def_CountingMatroid_Analysis_OmittedSlotQuadratic
import Definitions.Def_CountingMatroid_Analysis_OmittedTutteNormalization
import Definitions.Def_CountingMatroid_Analysis_QuadraticNonpositiveHyperplane
import Definitions.Def_CountingMatroid_Analysis_RankWeightQuadraticSignature
import Definitions.Def_CountingMatroid_Analysis_RankWeightSupportExchange
import Definitions.Def_CountingMatroid_Analysis_ScheduleConfidence
import Definitions.Def_CountingMatroid_Analysis_SlotBlockSignature
import Definitions.Def_CountingMatroid_Analysis_SquarefreeCoordinateHessian
import Definitions.Def_CountingMatroid_Analysis_ThreePairSignatureSchur
import Definitions.Def_CountingMatroid_Analysis_TransversalPartition
import Definitions.Def_CountingMatroid_Analysis_TransversalProjection
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
import Theorems.Thm_CountingMatroid_Analysis_DefectSlotSplitSignature_slot_total_pos
import Theorems.Thm_CountingMatroid_Analysis_OmittedSlotCoefficientFormula_slot_quadratic_state_sum
import Theorems.Thm_CountingMatroid_Analysis_OmittedSlotQuadratic_omitted_slot_descendant
import Theorems.Thm_CountingMatroid_Analysis_OmittedSlotQuadratic_omitted_slot_homogeneous
import Theorems.Thm_CountingMatroid_Analysis_OmittedTutteNormalization_normalized_omitted_slot
import Theorems.Thm_CountingMatroid_Analysis_RankWeightQuadraticSignature_branden_huh_quadratic_signature
import Theorems.Thm_CountingMatroid_Analysis_SlotBlockSignature_slot_block_nonpositive
import Theorems.Thm_CountingMatroid_Analysis_SlotOmissionPatternCharacterization_omission_pattern_iff

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
namespace CountingMatroid.Analysis.SlotOmissionPatternCharacterization
end CountingMatroid.Analysis.SlotOmissionPatternCharacterization
namespace CountingMatroid.Analysis.PairedRankValue
end CountingMatroid.Analysis.PairedRankValue
namespace CountingMatroid.Analysis.SignatureOrthogonalNonpositive
end CountingMatroid.Analysis.SignatureOrthogonalNonpositive
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
set_option autoImplicit false

/-!
The omitted-element quadratic input to the recursive slot transport. The
slot totals and old-hole matrix below follow main.tex:516-601. The numerical
split estimate and the real signature-to-orthogonal-nonpositivity implication
are proved. The explicit block matrix is assembled on the old holes and two
new coordinates. The dual-matroid omitted-label extraction is constructed;
its descendant, homogeneous degree, and exact normalization to the operational
omitted-rank polynomial are proved. The surviving omitted-label patterns
are identified exactly with the operational completion totals in all four
Hessian blocks, including the zero diagonals. The imported rank-weight
signature theorem and the proved block-form calculation give nonpositivity
on the balanced hyperplane and hence the recursive split bound.
-/

namespace CountingMatroid.Analysis.DefectSlotSplitSignature
end CountingMatroid.Analysis.DefectSlotSplitSignature
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.DefectSlotSplitSignature

open CountingMatroid.Model CountingMatroid.Program
open scoped BigOperators
open Classical

set_option maxHeartbeats 1000000 in
/-- PAPER: main.tex:584-625
For the actual operational rank weights, the extracted omitted-element
Hessian is nonpositive on the orthogonal complement of e_a+e_b. Its
old-old block is futureMatrix; the two mixed blocks are the opposite child
hole totals. This is the signature input, before the numerical split bound. -/
theorem solution (n r : ℕ) (M₁ M₂ : Matroid (Fin n))
    (o₁ o₂ : IndependenceOracle n) (q : ℚ)
    (hfull : FullGround M₁ M₂) (hr : CommonRank r M₁ M₂)
    (h₁ : ExactOracle M₁ o₁) (h₂ : ExactOracle M₂ o₂)
    (hq : 0 < q) (hqone : q ≤ 1)
    (B R : PairedSet n) (U : Finset (Fin n))
    (hBR : Disjoint B R)
    (hU : ∀ t ∈ U, ∀ b : Bool, (t, b) ∉ B ∧ (t, b) ∉ R)
    (hsize : B.card + R.card + U.card = n + 1)
    (t : Fin n) (ht : t ∈ U) :
    let sₐ := fun i => slotTotal r o₁ o₂ q B (insert (t, false) R) (U.erase t) i
    let sᵦ := fun i => slotTotal r o₁ o₂ q B (insert (t, true) R) (U.erase t) i
    let u := slotTotal r o₁ o₂ q B (insert (t, false) R) (U.erase t) (t, false)
    ∀ (h : PairedGround n → ℝ) (x y : ℝ),
      (∑ i ∈ R, (sₐ i + sᵦ i) * h i) + u * (x + y) = 0 →
      (∑ i ∈ R, ∑ j ∈ R, futureMatrix r o₁ o₂ q B R U t i j * h i * h j) +
        2 * x * (∑ i ∈ R, sᵦ i * h i) +
        2 * y * (∑ i ∈ R, sₐ i * h i) + 2 * u * x * y ≤ 0 := by
  classical
  intro sₐ sᵦ u h x y horth
  have hu : 0 < u := slot_total_pos r o₁ o₂ q hq B _ _ _
  let V : R → R → ℝ := fun i j => futureMatrix r o₁ o₂ q B R U t i j
  let a : R → ℝ := fun i => sₐ i
  let b : R → ℝ := fun i => sᵦ i
  have hsig : sigPos (SlotBlockSignature.slotBlockMatrix V a b u).toQuadraticForm' ≤ 1 := by
    let N := (DefectPartitionQuadraticExtraction.pairedMatroid M₁ M₂)✶
    let G := OmittedSlotQuadratic.omittedSlotQuadratic N q B R U t
    have hN : N.E = Set.univ := by
      simpa only [N, Matroid.dual_ground] using
        DefectPartitionQuadraticExtraction.paired_matroid_full_ground M₁ M₂ hfull
    have hdesc := OmittedSlotQuadratic.omitted_slot_descendant N q hq B R U t
    have hdegree := OmittedSlotQuadratic.omitted_slot_homogeneous
      N q B R U hBR hU hsize t ht
    have hentries : RankWeightQuadraticSignature.hessian G =
        SlotBlockSignature.slotBlockMatrix V a b u := by
      ext i j
      rw [RankWeightQuadraticSignature.hessian_coefficient]
      change ((MvPolynomial.coeff (Finsupp.single i 1 + Finsupp.single j 1)
        (OmittedSlotQuadratic.omittedSlotQuadratic N q B R U t) *
        (if i = j then 2 else 1) : ℚ) : ℝ) = _
      rw [OmittedTutteNormalization.normalized_omitted_slot
        r M₁ M₂ o₁ o₂ q hfull hr h₁ h₂ hq]
      rw [OmittedSlotCoefficientFormula.slot_quadratic_state_sum
        r o₁ o₂ q B R U hU t ht]
      simp_rw [SlotOmissionPatternCharacterization.omission_pattern_iff
        B R U hBR hU hsize t ht]
      have hnotpair (k : R) : (k : PairedGround n) ∉ ({(t, false), (t, true)} : PairedSet n) := by
        intro hk
        rcases Finset.mem_insert.mp hk with hk | hk
        · exact (hU t ht false).2 (hk ▸ k.property)
        · exact (hU t ht true).2 ((Finset.mem_singleton.mp hk) ▸ k.property)
      have hset_old (k l : R) :
          ((R ∪ {(t, false), (t, true)}).erase (k : PairedGround n)).erase l =
            (R.erase k).erase l ∪ {(t, false), (t, true)} := by
        rw [Finset.erase_union_distrib, Finset.erase_eq_of_notMem (hnotpair k),
          Finset.erase_union_distrib, Finset.erase_eq_of_notMem (hnotpair l)]
      have hpair (c : Bool) : ({(t, false), (t, true)} : PairedSet n).erase (t, c) =
          {(t, !c)} := by
        cases c <;> simp [Finset.erase_insert_of_ne, Prod.ext_iff]
      have hset_mixed (k : R) (c : Bool) :
          ((R ∪ {(t, false), (t, true)}).erase (k : PairedGround n)).erase (t, c) =
            (insert (t, !c) R).erase k := by
        rw [Finset.erase_union_distrib, Finset.erase_eq_of_notMem (hnotpair k),
          Finset.erase_union_distrib, hpair,
          Finset.erase_eq_of_notMem (by
            intro he
            exact (hU t ht c).2 (Finset.mem_of_mem_erase he))]
        have hn : (k : PairedGround n) ≠ (t, !c) := by
          intro hk
          exact (hU t ht (!c)).2 (hk ▸ k.property)
        rw [Finset.erase_insert_of_ne hn.symm]
        exact Finset.union_singleton _ _
      have hset_new :
          ((R ∪ {(t, false), (t, true)}).erase (t, false)).erase (t, true) = R := by
        rw [Finset.erase_union_distrib, hpair false,
          Finset.erase_eq_of_notMem (hU t ht false).2,
          Finset.erase_union_distrib, Finset.erase_eq_of_notMem (hU t ht true).2]
        simp
      have hcompletion (S : PairedSet n) (W : Finset (Fin n))
          (hole : PairedGround n) (state : PairedSet n) (w : ℝ) :
          (if (∃ choices : Fin n → Bool,
            state = B ∪ S.erase hole ∪ W.image (fun t => (t, choices t))) then w else 0) =
            if SlotCompletion B S W hole state then w else 0 := by
        by_cases hs : SlotCompletion B S W hole state
        · have hs₂ : ∃ choices : Fin n → Bool,
              state = B ∪ S.erase hole ∪ W.image (fun t => (t, choices t)) := hs
          rw [if_pos hs, if_pos hs₂]
        · have hs₂ : ¬ ∃ choices : Fin n → Bool,
              state = B ∪ S.erase hole ∪ W.image (fun t => (t, choices t)) := hs
          rw [if_neg hs, if_neg hs₂]
      have hset_mixed_rev (k : R) (c : Bool) :
          ((R ∪ {(t, false), (t, true)}).erase (t, c)).erase (k : PairedGround n) =
            (insert (t, !c) R).erase k := by
        rw [Finset.erase_right_comm, hset_mixed]
      have hset_new_rev :
          ((R ∪ {(t, false), (t, true)}).erase (t, true)).erase (t, false) = R := by
        rw [Finset.erase_right_comm, hset_new]
      cases i with
      | inl i =>
        cases j with
        | inl j =>
          by_cases hij : i = j
          · subst j
            simp [SlotBlockSignature.slotBlockMatrix, V, futureMatrix]
          · have hijv : (i : PairedGround n) ≠ (j : PairedGround n) :=
              Subtype.val_injective.ne hij
            simp only [SlotBlockSignature.slotBlockMatrix, V, futureMatrix,
              ne_eq, Sum.inl.injEq, hij, hijv, not_false_eq_true, true_and, ite_false, mul_one,
              OmittedSlotCoefficientFormula.activeLabel, Sum.elim_inl]
            simp only [hset_old, Finset.union_assoc]
            simp only [Rat.cast_sum, apply_ite (fun z : ℚ => (z : ℝ)), Rat.cast_zero]
        | inr c =>
          cases c <;>
            simp only [SlotBlockSignature.slotBlockMatrix, a, b, sₐ, sᵦ, slotTotal,
              ne_eq, Sum.inl_ne_inr, not_false_eq_true, true_and, Bool.false_eq_true, ite_false,
              ite_true, mul_one, OmittedSlotCoefficientFormula.activeLabel,
              Sum.elim_inl, Sum.elim_inr, hset_mixed, Bool.not_false, Bool.not_true] <;>
            simp only [Rat.cast_sum, apply_ite (fun z : ℚ => (z : ℝ)), Rat.cast_zero, hcompletion]
      | inr c =>
        cases j with
        | inl j =>
          cases c <;>
            simp only [SlotBlockSignature.slotBlockMatrix, a, b, sₐ, sᵦ, slotTotal,
              ne_eq, Sum.inr_ne_inl, not_false_eq_true, true_and, Bool.false_eq_true, ite_false,
              ite_true, mul_one, OmittedSlotCoefficientFormula.activeLabel,
              Sum.elim_inl, Sum.elim_inr, hset_mixed_rev, Bool.not_false, Bool.not_true] <;>
            simp only [Rat.cast_sum, apply_ite (fun z : ℚ => (z : ℝ)), Rat.cast_zero, hcompletion]
        | inr d =>
          cases c <;> cases d <;>
            simp only [SlotBlockSignature.slotBlockMatrix, u, slotTotal, SlotCompletion,
              ne_eq, Sum.inr.injEq, Bool.false_eq_true, Bool.true_eq_false, not_false_eq_true,
              not_true_eq_false, true_and, false_and, ite_false, ite_true, mul_one,
              Finset.sum_const_zero, Rat.cast_zero, zero_mul,
              OmittedSlotCoefficientFormula.activeLabel, Sum.elim_inr, hset_new, hset_new_rev,
              Finset.erase_insert (hU t ht false).2] <;>
            simp only [Rat.cast_sum, apply_ite (fun z : ℚ => (z : ℝ)), Rat.cast_zero]
    rw [← hentries]
    exact RankWeightQuadraticSignature.branden_huh_quadratic_signature
      N hN q hq hqone G hdesc hdegree
  have hbalance : (∑ i : R, (a i + b i) * h i) + u * (x + y) = 0 := by
    change (∑ i : R, (sₐ i + sᵦ i) * h i) + u * (x + y) = 0
    rw [Finset.sum_coe_sort R (fun i => (sₐ i + sᵦ i) * h i)]
    exact horth
  have hnonpos := SlotBlockSignature.slot_block_nonpositive V a b u hu hsig
    (fun i => h i) x y hbalance
  dsimp only [V, a, b] at hnonpos
  have hinner (i : PairedGround n) :
      (∑ j : R, futureMatrix r o₁ o₂ q B R U t i j * h i * h j) =
      ∑ j ∈ R, futureMatrix r o₁ o₂ q B R U t i j * h i * h j :=
    Finset.sum_coe_sort R (fun j => futureMatrix r o₁ o₂ q B R U t i j * h i * h j)
  simp_rw [hinner] at hnonpos
  rw [Finset.sum_coe_sort R (fun i => ∑ j ∈ R,
      futureMatrix r o₁ o₂ q B R U t i j * h i * h j),
    Finset.sum_coe_sort R (fun i => sᵦ i * h i),
    Finset.sum_coe_sort R (fun i => sₐ i * h i)] at hnonpos
  exact hnonpos
