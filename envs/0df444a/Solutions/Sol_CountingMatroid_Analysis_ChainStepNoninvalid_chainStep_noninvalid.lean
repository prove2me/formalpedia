-- Prove2me | solution 1 for CountingMatroid.Analysis.ChainStepNoninvalid.chainStep_noninvalid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T15:05:58.955838+00:00
-- url     : https://prove2.me/submissions/c9fd152b-22d6-48e5-b67d-039c91ae29f8

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
import Definitions.Def_CountingMatroid_Analysis_BoundedUniformReplay
import Definitions.Def_CountingMatroid_Analysis_ChainStepIntervalReplay
import Definitions.Def_CountingMatroid_Model_Operations
import Definitions.Def_CountingMatroid_Model_Prelude
import Definitions.Def_CountingMatroid_Model_Program
import Definitions.Def_CountingMatroid_Model_Subroutines
import Lean
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Int
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
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF

namespace CountingMatroid.Analysis.ChainStepNoninvalid
end CountingMatroid.Analysis.ChainStepNoninvalid
namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
set_option autoImplicit false

/-!
A successful operational chain attempt preserves non-invalid classification.
An invalid proposal is rejected; each other success returns either the valid
old state or the proposal whose classifier was checked. This statement does
not claim that every failure is a capped draw failure.
-/

namespace CountingMatroid.Analysis.ChainStepNoninvalid
end CountingMatroid.Analysis.ChainStepNoninvalid
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.ChainStepNoninvalid

open CountingMatroid.Model CountingMatroid.Program

/-- INTERNAL: A successful attempt preserves non-invalid classification,
including rejected proposals and the lazy holding branch.
TEXLINE: main.tex:746-768 -/
theorem solution {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (tape : ℕ → Bool)
    (trials : ℕ) (q : ℚ) (weights : Multipliers n)
    (state : PairedSet n) (cursor : ℕ) (result : PairedSet n × ℕ)
    (hvalid : (classifyState state).val ≠ .invalid)
    (h : (chainStep r o₁ o₂ tape trials q weights state cursor).val = some result) :
    (classifyState result.1).val ≠ .invalid := by
  unfold chainStep at h
  simp only [Arlib.Computation.Charged.val_bind] at h
  split at h
  · have heq := Option.some.inj h
    rw [← heq]
    exact hvalid
  · simp only [Arlib.Computation.Charged.val_bind] at h
    split at h
    · cases h
    · simp only [Arlib.Computation.Charged.val_bind] at h
      split at h
      · cases h
      · simp only [Arlib.Computation.Charged.val_bind] at h
        split at h
        · simp only [Arlib.Computation.Charged.val_bind] at h
          split at h
          · have heq := Option.some.inj h
            rw [← heq]
            exact hvalid
          · rename_i kind hkind
            simp only [Arlib.Computation.Charged.val_bind] at h
            split at h
            · simp only [Arlib.Computation.Charged.val_bind] at h
              split at h
              · simp only [Arlib.Computation.Charged.val_bind] at h
                split at h
                · cases h
                · simp only [Arlib.Computation.Charged.val_bind] at h
                  split at h
                  all_goals
                    have heq := Option.some.inj h
                    rw [← heq]
                    first | exact hkind | exact hvalid
              · have heq := Option.some.inj h
                rw [← heq]
                exact hkind
            · cases h
        · cases h
