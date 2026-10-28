-- Prove2me | solution 1 for CountingMatroid.Analysis.OmittedRankWeightPolynomial.omitted_rank_coefficient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T14:52:35.44204+00:00
-- url     : https://prove2.me/submissions/0e931f1b-5ac3-45cf-a26d-6096696fbe9e

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
import Definitions.Def_CountingMatroid_Analysis_FirstPhaseFailure
import Definitions.Def_CountingMatroid_Analysis_InitialMultipliersGood
import Definitions.Def_CountingMatroid_Analysis_OmittedRankWeightPolynomial
import Definitions.Def_CountingMatroid_Analysis_ScheduleConfidence
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
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Data.BitVec
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finsupp.Indicator
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Induction
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sort
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Data.Set.Finite.List
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF

namespace CountingMatroid.Interface
end CountingMatroid.Interface
namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
namespace CountingMatroid.Analysis.TransversalRankBridge
end CountingMatroid.Analysis.TransversalRankBridge
namespace CountingMatroid.Analysis.GreedyRankCorrect
end CountingMatroid.Analysis.GreedyRankCorrect
section


set_option autoImplicit false

/-!
The omitted-element rank-weight polynomial, expressed using the operational
paired-rank scan. Its coefficients below are identified with the operational
conditional defect totals. These identities do not assert a Hessian signature
or identify this scan with the rank of a matroid.
-/

namespace CountingMatroid.Analysis.OmittedRankWeightPolynomial

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.ConditionalDefectCoefficients
open scoped BigOperators
open Classical



/-- INTERNAL: Each omitted label occurs once, and every selected label has
exponent zero.
TEXLINE: main.tex:571-625 -/
theorem omitted_exponent_apply {n : ℕ} (state : PairedSet n) (e : PairedGround n) :
    omittedExponent state e = if e ∈ state then 0 else 1 := by
  classical
  simp [omittedExponent]

/-- INTERNAL: Omitted-label exponent vectors recover the entire paired state.
TEXLINE: main.tex:571-625 -/
theorem omitted_exponent_injective {n : ℕ} :
    Function.Injective (@omittedExponent n) := by
  classical
  intro state next h
  ext e
  have he := DFunLike.congr_fun h e
  rw [omitted_exponent_apply, omitted_exponent_apply] at he
  by_cases hs : e ∈ state <;> by_cases ht : e ∈ next <;> simp_all

















end CountingMatroid.Analysis.OmittedRankWeightPolynomial

end
set_option autoImplicit false

/-!
The omitted-element rank-weight polynomial, expressed using the operational
paired-rank scan. Its coefficients below are identified with the operational
conditional defect totals. These identities do not assert a Hessian signature
or identify this scan with the rank of a matroid.
-/

namespace CountingMatroid.Analysis.OmittedRankWeightPolynomial
end CountingMatroid.Analysis.OmittedRankWeightPolynomial
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.OmittedRankWeightPolynomial

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.ConditionalDefectCoefficients
open scoped BigOperators
open Classical

/-- INTERNAL: The squarefree coefficient indexed by a state's omitted
labels is its exact operational rank weight, guarded only by cardinality.
TEXLINE: main.tex:571-625 -/
theorem solution {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (q : ℚ) (state : PairedSet n) :
    MvPolynomial.coeff (omittedExponent state) (omittedRankPolynomial r o₁ o₂ q) =
      if state.card = n then
        q ^ (n - (CountingMatroid.Model.Subroutines.pairedRank r o₁ o₂ state).val)
      else 0 := by
  classical
  unfold omittedRankPolynomial
  rw [MvPolynomial.coeff_sum]
  have hterm (next : PairedSet n) :
      MvPolynomial.coeff (omittedExponent state)
        (if next.card = n then MvPolynomial.monomial (omittedExponent next)
          (q ^ (n - (CountingMatroid.Model.Subroutines.pairedRank r o₁ o₂ next).val))
        else 0) =
      if next = state then
        (if next.card = n then
          q ^ (n - (CountingMatroid.Model.Subroutines.pairedRank r o₁ o₂ next).val)
        else 0) else 0 := by
    have heq : omittedExponent next = omittedExponent state ↔ next = state :=
      omitted_exponent_injective.eq_iff
    by_cases hc : next.card = n <;> simp [hc, MvPolynomial.coeff_monomial, heq]
  simp_rw [hterm]
  simp
