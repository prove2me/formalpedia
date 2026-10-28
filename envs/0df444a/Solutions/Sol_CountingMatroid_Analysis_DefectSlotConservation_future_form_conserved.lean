-- Prove2me | solution 1 for CountingMatroid.Analysis.DefectSlotConservation.future_form_conserved
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T15:24:22.019361+00:00
-- url     : https://prove2.me/submissions/3e2fe8f4-0cb9-423f-80fc-d8fea69bda67

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
import Definitions.Def_CountingMatroid_Analysis_DefectSlotConservation
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
import Theorems.Thm_CountingMatroid_Analysis_DefectSlotConservation_future_matrix_split

namespace CountingMatroid.Analysis.SlotOmissionPatternCharacterization
end CountingMatroid.Analysis.SlotOmissionPatternCharacterization
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
namespace CountingMatroid.Analysis.SignatureOrthogonalNonpositive
end CountingMatroid.Analysis.SignatureOrthogonalNonpositive
section


set_option autoImplicit false

/-!
Binary completion identities used by the balanced-hole recursion. Processing
one ordinary pair partitions each old-hole completion into its two children.
The corresponding future-slot matrix identities give conservation of the
future quadratic forms; these identities use finite sets, not a signature
assumption.
-/

namespace CountingMatroid.Analysis.DefectSlotConservation

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.DefectSlotSplitSignature
open scoped BigOperators















/-- INTERNAL: The future-slot matrix is symmetric because its completion
predicate omits the same two holes in either order.
TEXLINE: main.tex:571-579 -/
theorem future_matrix_symmetric {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (q : ℚ)
    (B R : PairedSet n) (U : Finset (Fin n)) (s : Fin n)
    (i j : PairedGround n) :
    futureMatrix r o₁ o₂ q B R U s i j =
      futureMatrix r o₁ o₂ q B R U s j i := by
  classical
  by_cases hij : i = j
  · subst j
    rfl
  have herase : (R.erase i).erase j = (R.erase j).erase i := by
    ext x
    simp only [Finset.mem_erase]
    tauto
  simp only [futureMatrix, if_neg hij, if_neg (Ne.symm hij), herase]

/-- PAPER: main.tex:636-639
A future matrix entry between an old hole and the new hole counts the same
states in either child, since the newly processed pair is then empty. -/
theorem future_matrix_new_hole_eq {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (q : ℚ)
    (B R : PairedSet n) (U : Finset (Fin n)) (t s : Fin n)
    (hfree : ∀ c : Bool, (t, c) ∉ R)
    (i : PairedGround n) (hi : i ∈ R) :
    futureMatrix r o₁ o₂ q B (insert (t, false) R) (U.erase t) s i (t, false) =
      futureMatrix r o₁ o₂ q B (insert (t, true) R) (U.erase t) s i (t, true) := by
  classical
  have hne (c : Bool) : i ≠ (t, c) := by
    rintro rfl
    exact hfree c hi
  have hn (c : Bool) : (t, c) ∉ R.erase i := by
    exact fun h => hfree c (Finset.mem_of_mem_erase h)
  simp only [futureMatrix, if_neg (hne _),
    Finset.erase_insert_of_ne (hne _).symm, Finset.erase_insert (hn _)]

/-- INTERNAL: Expand a zero-diagonal symmetric quadratic on one newly
inserted hole into its old quadratic and the old–new cross term.
TEXLINE: main.tex:632-640 -/
private theorem child_quadratic_expansion {α : Type*} [DecidableEq α]
    (R : Finset α) (p : α) (hp : p ∉ R) (M : α → α → ℝ)
    (hsym : ∀ i j, M i j = M j i) (hdiag : M p p = 0) (h : α → ℝ) :
    (∑ i ∈ insert p R, ∑ j ∈ insert p R, M i j * h i * h j) =
      (∑ i ∈ R, ∑ j ∈ R, M i j * h i * h j) +
        2 * h p * (∑ i ∈ R, M i p * h i) := by
  classical
  simp only [Finset.sum_insert hp, hdiag, zero_mul, zero_add,
    Finset.sum_add_distrib]
  have hcross : (∑ i ∈ R, M p i * h p * h i) =
      h p * (∑ i ∈ R, M i p * h i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hsym p i]
    ring
  have hcross' : (∑ i ∈ R, M i p * h i * h p) =
      h p * (∑ i ∈ R, M i p * h i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hcross, hcross']
  ring









end CountingMatroid.Analysis.DefectSlotConservation

end
set_option autoImplicit false

/-!
Binary completion identities used by the balanced-hole recursion. Processing
one ordinary pair partitions each old-hole completion into its two children.
The corresponding future-slot matrix identities give conservation of the
future quadratic forms; these identities use finite sets, not a signature
assumption.
-/

namespace CountingMatroid.Analysis.DefectSlotConservation
end CountingMatroid.Analysis.DefectSlotConservation
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.DefectSlotConservation

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.DefectSlotSplitSignature
open scoped BigOperators

/-- PAPER: main.tex:628-641
Future-slot quadratic forms are conserved by an earlier split whenever
old-hole values stay fixed and the two new-hole values are opposite. -/
theorem solution {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (q : ℚ)
    (B R : PairedSet n) (U : Finset (Fin n))
    (t s : Fin n) (ht : t ∈ U) (hts : t ≠ s)
    (hfree : ∀ c : Bool, (t, c) ∉ B ∧ (t, c) ∉ R)
    (h hₐ hᵦ : PairedGround n → ℝ)
    (hkeepₐ : ∀ i ∈ R, hₐ i = h i) (hkeepᵦ : ∀ i ∈ R, hᵦ i = h i)
    (hopp : hₐ (t, false) + hᵦ (t, true) = 0) :
    (∑ i ∈ insert (t, false) R, ∑ j ∈ insert (t, false) R,
      futureMatrix r o₁ o₂ q B (insert (t, false) R) (U.erase t) s i j * hₐ i * hₐ j) +
    (∑ i ∈ insert (t, true) R, ∑ j ∈ insert (t, true) R,
      futureMatrix r o₁ o₂ q B (insert (t, true) R) (U.erase t) s i j * hᵦ i * hᵦ j) =
    ∑ i ∈ R, ∑ j ∈ R, futureMatrix r o₁ o₂ q B R U s i j * h i * h j := by
  classical
  let Mₐ := futureMatrix r o₁ o₂ q B (insert (t, false) R) (U.erase t) s
  let Mᵦ := futureMatrix r o₁ o₂ q B (insert (t, true) R) (U.erase t) s
  rw [child_quadratic_expansion R (t, false) (hfree false).2 Mₐ
      (future_matrix_symmetric r o₁ o₂ q B _ _ s) (by simp [Mₐ, futureMatrix]) hₐ,
    child_quadratic_expansion R (t, true) (hfree true).2 Mᵦ
      (future_matrix_symmetric r o₁ o₂ q B _ _ s) (by simp [Mᵦ, futureMatrix]) hᵦ]
  have hold (M : PairedGround n → PairedGround n → ℝ)
      (h' : PairedGround n → ℝ) (hkeep : ∀ i ∈ R, h' i = h i) :
      (∑ i ∈ R, ∑ j ∈ R, M i j * h' i * h' j) =
        ∑ i ∈ R, ∑ j ∈ R, M i j * h i * h j := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hkeep i hi, hkeep j hj]
  have hcross : (∑ i ∈ R, Mᵦ i (t, true) * hᵦ i) =
      ∑ i ∈ R, Mₐ i (t, false) * hₐ i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hkeepₐ i hi, hkeepᵦ i hi]
    dsimp only [Mₐ, Mᵦ]
    rw [future_matrix_new_hole_eq r o₁ o₂ q B R U t s
      (fun c => (hfree c).2) i hi]
  rw [hold Mₐ hₐ hkeepₐ, hold Mᵦ hᵦ hkeepᵦ, hcross]
  have hcancel : 2 * hₐ (t, false) * (∑ i ∈ R, Mₐ i (t, false) * hₐ i) +
      2 * hᵦ (t, true) * (∑ i ∈ R, Mₐ i (t, false) * hₐ i) = 0 := by
    rw [← add_mul, ← mul_add, hopp, mul_zero, zero_mul]
  calc
    _ = (∑ i ∈ R, ∑ j ∈ R, Mₐ i j * h i * h j) +
        (∑ i ∈ R, ∑ j ∈ R, Mᵦ i j * h i * h j) := by linarith [hcancel]
    _ = _ := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      rw [← add_mul, ← add_mul]
      dsimp only [Mₐ, Mᵦ]
      rw [future_matrix_split r o₁ o₂ q B R U t s ht hts hfree i j hi hj]
