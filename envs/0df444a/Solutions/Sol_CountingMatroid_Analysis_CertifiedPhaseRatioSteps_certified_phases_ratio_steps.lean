-- Prove2me | solution 1 for CountingMatroid.Analysis.CertifiedPhaseRatioSteps.certified_phases_ratio_steps
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T15:45:31.370991+00:00
-- url     : https://prove2.me/submissions/0d565182-6e4c-4216-8c4f-7c6e4f28db45

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
import Definitions.Def_CountingMatroid_Analysis_FirstPhaseFailure
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
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic
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
namespace CountingMatroid.Analysis.CertifiedPhaseRatioSteps
end CountingMatroid.Analysis.CertifiedPhaseRatioSteps
section


set_option autoImplicit false

/-!
The phase history below is the value of each prefix of the actual bounded-run
fold, including its absorbing aborted state. Successful local ratio steps
give the product witness used by the lower-tail proof. This is a
deterministic operational representation, not a phase probability estimate.
-/

namespace CountingMatroid.Analysis.BoundedRunPhaseHistory

open CountingMatroid.Model CountingMatroid.Model.Operations
open CountingMatroid.Program CountingMatroid.Analysis.BoundedRunPhase





/-- INTERNAL: Split a charged fold at a prefix while retaining its actual value. -/
private theorem val_foldl_append {α β : Type}
    (f : β → α → Arlib.Computation.Charged Op Cell β)
    (xs ys : List α) (b : β) :
    (Arlib.Computation.Charged.foldl f (xs ++ ys) b).val =
      (Arlib.Computation.Charged.foldl f ys
        (Arlib.Computation.Charged.foldl f xs b).val).val := by
  induction xs generalizing b with
  | nil => rfl
  | cons x xs ih =>
      simpa only [List.cons_append, Arlib.Computation.Charged.val_foldl_cons]
        using ih (f b x).val

/-- INTERNAL: Consecutive history entries are related by the actual phase
body, with the previously reached tables, weights, product and bit cursor.
TEXLINE: main.tex:1160-1205 -/
theorem phaseHistory_succ {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (j : ℕ) :
    phaseHistory r o₁ o₂ tape s (j + 1) =
      (boundedRunPhase r o₁ o₂ tape s j
        (phaseHistory r o₁ o₂ tape s j)).val := by
  unfold phaseHistory Arlib.Computation.Charged.repeatFor
  rw [List.range_succ, val_foldl_append]
  rfl











end CountingMatroid.Analysis.BoundedRunPhaseHistory

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r18 · proved · represented actual phase-fold prefixes; proved their successor relation and final-output equality, reconstructed an accurate-ratio witness from successful local steps, and covered witness failure by the first failed phase. No probability estimate or unproved declaration introduced.
-/

end
set_option autoImplicit false

namespace CountingMatroid.Analysis.CertifiedPhaseRatioSteps
end CountingMatroid.Analysis.CertifiedPhaseRatioSteps
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.CertifiedPhaseRatioSteps

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.BoundedRunPhase
open CountingMatroid.Analysis.BoundedRunPhaseHistory

/-- INTERNAL: The stronger phase certificates used by conditional probability
analysis imply the local ratio steps of the actual operational history.
Positivity of every reached product is proved from initialization and the
certified ratio bounds; it is not an extra hypothesis on completed runs.
TEXLINE: main.tex:1273-1304 -/
theorem solution {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (p : InputParams) (hn : 0 < n)
    (tape : ℕ → Bool)
    (hcert : ∀ j < (CountingMatroid.Interface.Pseudocode.setup n p).L,
      FirstPhaseFailure.CertifiedPhase r o₁ o₂ tape
        (CountingMatroid.Interface.Pseudocode.setup n p) j) :
    ∀ j < (CountingMatroid.Interface.Pseudocode.setup n p).L,
      PhaseRatioStep r o₁ o₂ p tape j := by
  let s := CountingMatroid.Interface.Pseudocode.setup n p
  let C := fun j => TransversalPartition.partitionSum r o₁ o₂ (s.ρ ^ j)
  change ∀ j < s.L, FirstPhaseFailure.CertifiedPhase r o₁ o₂ tape s j at hcert
  have hρ : 0 < s.ρ := by
    change 0 < 1 - 1 / ((2 * n : ℕ) : ℚ)
    push_cast
    have hnq : (1 : ℚ) ≤ n := by exact_mod_cast hn
    apply sub_pos.mpr
    apply (div_lt_one (by positivity : (0 : ℚ) < 2 * n)).mpr
    linarith
  have hη : s.η = p.ε / (32 * ((s.L : ℚ) + 1)) := by
    change p.ε / ((32 * (s.L + 1) : ℕ) : ℚ) = _
    push_cast
    rfl
  have hηpos : 0 < s.η := by
    rw [hη]
    exact div_pos p.ε_pos (by positivity)
  have hηsmall : s.η < 1 := by
    rw [hη]
    apply (div_lt_one (by positivity : (0 : ℚ) < 32 * ((s.L : ℚ) + 1))).mpr
    have hL : (0 : ℚ) ≤ s.L := Nat.cast_nonneg _
    linarith [p.ε_lt_one]
  have hC : ∀ j, 0 < C j := by
    intro j
    apply Finset.sum_pos
    · intro A _
      exact pow_pos (pow_pos hρ j) _
    · exact Finset.univ_nonempty
  have hratioPos (j : ℕ) (ratio : ℚ)
      (hl : (1 - s.η) / (1 + s.η) ≤ ratio / (C (j + 1) / C j)) :
      0 < ratio := by
    have hden : 0 < C (j + 1) / C j := div_pos (hC _) (hC _)
    have hlo : 0 < (1 - s.η) / (1 + s.η) :=
      div_pos (sub_pos.mpr hηsmall) (by linarith)
    exact (mul_pos hlo hden).trans_le ((le_div_iff₀ hden).mp hl)
  have hstates (k : ℕ) (hk : k ≤ s.L) :
      ∃ current : AnnealingCursor n,
        phaseHistory r o₁ o₂ tape s k = some current ∧ 0 < current.product := by
    induction k with
    | zero => exact ⟨initialCursor n s, rfl, by norm_num [initialCursor]⟩
    | succ k ih =>
        obtain ⟨previous, hprevious, hpositive⟩ := ih (by omega)
        obtain ⟨ratio, hl, _, current, next, hcurrent, hnext, hmul, _⟩ :=
          hcert k (by omega)
        change phaseHistory r o₁ o₂ tape s k = some current at hcurrent
        have heq : current = previous :=
          Option.some.inj (hcurrent.symm.trans hprevious)
        subst current
        refine ⟨next, ?_, ?_⟩
        · rw [phaseHistory_succ, hprevious]
          exact hnext
        · rw [hmul]
          exact mul_pos hpositive (hratioPos k ratio hl)
  change ∀ j < s.L, PhaseRatioStep r o₁ o₂ p tape j
  intro j hj
  obtain ⟨previous, hprevious, hpositive⟩ := hstates j (by omega)
  obtain ⟨ratio, hl, hu, current, next, hcurrent, hnext, hmul, _⟩ := hcert j hj
  change phaseHistory r o₁ o₂ tape s j = some current at hcurrent
  have heq : current = previous := Option.some.inj (hcurrent.symm.trans hprevious)
  subst current
  have hnpos : 0 < next.product := by
    rw [hmul]
    exact mul_pos hpositive (hratioPos j ratio hl)
  have hquot : next.product / previous.product = ratio := by
    rw [hmul, mul_div_cancel_left₀ _ hpositive.ne']
  refine ⟨previous, next, hprevious, hnext, hpositive, hnpos, ?_⟩
  simpa only [hquot] using And.intro hl hu
