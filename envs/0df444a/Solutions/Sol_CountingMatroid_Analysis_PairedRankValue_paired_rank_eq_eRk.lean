-- Prove2me | solution 1 for CountingMatroid.Analysis.PairedRankValue.paired_rank_eq_eRk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T15:54:49.863996+00:00
-- url     : https://prove2.me/submissions/597630e6-5149-4d06-bf9b-db782d3b76e5

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
import Definitions.Def_CountingMatroid_Analysis_CubicTensorContraction
import Definitions.Def_CountingMatroid_Analysis_DefectPartitionQuadraticConstruction
import Definitions.Def_CountingMatroid_Analysis_FirstPhaseFailure
import Definitions.Def_CountingMatroid_Analysis_InitialMultipliersGood
import Definitions.Def_CountingMatroid_Analysis_LorentzianDirectionalSignature
import Definitions.Def_CountingMatroid_Analysis_QuadraticNonpositiveHyperplane
import Definitions.Def_CountingMatroid_Analysis_RankWeightQuadraticSignature
import Definitions.Def_CountingMatroid_Analysis_RankWeightSupportExchange
import Definitions.Def_CountingMatroid_Analysis_ScheduleConfidence
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
import Mathlib.Algebra.MvPolynomial.PDeriv
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
import Theorems.Thm_CountingMatroid_Analysis_PairedRankValue_paired_matroid_eRk
import Theorems.Thm_CountingMatroid_Analysis_PairedRankValue_paired_rank_value

namespace CountingMatroid.Analysis.PairedRankValue
end CountingMatroid.Analysis.PairedRankValue
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
set_option autoImplicit false

/-!
The value of the paired-rank program on an arbitrary paired set, expressed
through the two original matroid ranks. This evaluates the charged projection
scan as well as its two greedy scans, without introducing a rank oracle.
-/

namespace CountingMatroid.Analysis.PairedRankValue
end CountingMatroid.Analysis.PairedRankValue
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.PairedRankValue

open CountingMatroid.Model
open CountingMatroid.Model.Subroutines
open CountingMatroid.Analysis.DefectPartitionQuadraticExtraction

/-- PAPER: main.tex:270-280
The paired-rank program computes the rank of the paired matroid on every
paired set, using only the two supplied original independence oracles. -/
theorem solution {n : ℕ} (r : ℕ) (M₁ M₂ : Matroid (Fin n))
    (o₁ o₂ : IndependenceOracle n) (hfull : FullGround M₁ M₂)
    (hr : CommonRank r M₁ M₂) (h₁ : ExactOracle M₁ o₁)
    (h₂ : ExactOracle M₂ o₂) (state : PairedSet n) :
    (pairedRank r o₁ o₂ state).val =
      ((pairedMatroid M₁ M₂).eRk (state : Set (PairedGround n))).toNat := by
  classical
  let Y : Set (Fin n) := {i | (i, true) ∈ state}
  let Z : Set (Fin n) := {i | (i, true) ∉ state}
  have hfinite (M : Matroid (Fin n)) (S : Set (Fin n)) : M.eRk S ≠ ⊤ :=
    (M.isRkFinite_of_finite (Set.toFinite S)).eRk_lt_top.ne
  have hcard : Y.encard =
      ((Finset.univ.filter (fun i => (i, true) ∈ state)).card : ℕ∞) := by
    have hs : Y = (Finset.univ.filter (fun i => (i, true) ∈ state) : Set (Fin n)) := by
      ext i
      simp [Y]
    rw [hs]
    exact Set.encard_coe_eq_coe_finsetCard _
  have hcompl : M₂.E \ Y = Z := by
    rw [hfull.2]
    ext i
    simp [Y, Z]
  have hd := M₂.eRk_dual_add_eRank Y (by rw [hfull.2]; exact Set.subset_univ _)
  rw [hr.2, hcompl, hcard] at hd
  have hd' : (M₂✶.eRk Y).toNat + r =
      (M₂.eRk Z).toNat + (Finset.univ.filter (fun i => (i, true) ∈ state)).card := by
    have hh := congrArg ENat.toNat hd
    simpa only [ENat.toNat_add (hfinite M₂✶ Y) (ENat.coe_ne_top r),
      ENat.toNat_add (hfinite M₂ Z) (ENat.coe_ne_top _), ENat.toNat_natCast] using hh
  rw [paired_rank_value r M₁ M₂ o₁ o₂ hfull h₁ h₂,
    paired_matroid_eRk M₁ M₂ hfull,
    ENat.toNat_add (hfinite M₁ _) (hfinite M₂✶ _)]
  change (M₁.eRk _).toNat + _ + (M₂.eRk Z).toNat - r =
    (M₁.eRk _).toNat + (M₂✶.eRk Y).toNat
  simp only [Finset.mem_coe]
  omega
