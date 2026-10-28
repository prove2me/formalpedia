-- Prove2me | solution 1 for CountingMatroid.Analysis.ChainStepIntervalReplay.chainStep_success_interval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T15:36:52.624031+00:00
-- url     : https://prove2.me/submissions/a5aec114-ac92-4106-9e34-2141f971b46f

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
import Theorems.Thm_CountingMatroid_Analysis_BoundedUniformReplay_boundedUniform_interval_replay

namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
set_option autoImplicit false

/-!
Success-path replay for the charged chain step. A successful transition has
a monotone cursor and depends only on its consumed bit interval. The generic
option-fold lemma also retains the program's absorbing abort state.
-/

namespace CountingMatroid.Analysis.ChainStepIntervalReplay
end CountingMatroid.Analysis.ChainStepIntervalReplay
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.ChainStepIntervalReplay
open CountingMatroid.Model CountingMatroid.Model.Operations CountingMatroid.Program
open CountingMatroid.Analysis.BoundedUniformReplay

/-- INTERNAL: A successful underlying chain transition reads only its consumed
interval and never moves the fair-bit cursor backwards.
TEXLINE: main.tex:746-768,1392-1421 -/
theorem solution {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (trials : ℕ) (q : ℚ)
    (weights : Multipliers n) (state : PairedSet n) (start : ℕ) :
    SuccessReplay (fun tape => (chainStep r o₁ o₂ tape trials q weights state start).val)
      Prod.snd start := by
  intro tape out hrun
  unfold chainStep at hrun ⊢
  simp +instances only [Arlib.Computation.Charged.val_bind, fairBit, successor,
    Arlib.Computation.Charged.val_op] at hrun
  cases hhold : tape start with
  | true =>
      simp +instances only [hhold, ite_true, Arlib.Computation.Charged.val_pure] at hrun
      have hout : (state, start + 1) = out := Option.some.inj hrun
      subst out
      refine ⟨Nat.le_succ _, ?_⟩
      intro other hagree
      have hb : other start = true := (hagree start le_rfl (Nat.lt_succ_self _)).symm.trans hhold
      simp +instances only [chainStep, Arlib.Computation.Charged.val_bind, fairBit, successor,
        Arlib.Computation.Charged.val_op, hb, ite_true, Arlib.Computation.Charged.val_pure]
  | false =>
      simp +instances only [hhold, Bool.false_eq_true, ite_false] at hrun
      cases hdrawA : (boundedUniform tape trials n (start + 1)).val with
      | mk choiceA stopA =>
        cases choiceA with
        | none =>
          simp +instances only [hdrawA, Arlib.Computation.Charged.val_bind, Arlib.Computation.Charged.val_pure] at hrun
          contradiction
        | some aIndex =>
          simp +instances only [hdrawA, Arlib.Computation.Charged.val_bind] at hrun
          cases hdrawB : (boundedUniform tape trials n stopA).val with
          | mk choiceB stopB =>
            cases choiceB with
            | none =>
              simp +instances only [hdrawB, Arlib.Computation.Charged.val_bind, Arlib.Computation.Charged.val_pure] at hrun
              contradiction
            | some bIndex =>
              simp +instances only [hdrawB, Arlib.Computation.Charged.val_bind] at hrun
              have hA := boundedUniform_interval_replay trials n (start + 1) tape
              have hB := boundedUniform_interval_replay trials n stopA tape
              simp +instances only [hdrawA] at hA
              simp +instances only [hdrawB] at hB
              have hstartB : start ≤ stopB := (Nat.le_succ _).trans (hA.1.trans hB.1)
              have replayDraws (other : ℕ → Bool)
                  (hstop : stopB ≤ out.2)
                  (hagree : ∀ i, start ≤ i → i < out.2 → tape i = other i) :
                  other start = false ∧
                  (boundedUniform other trials n (start + 1)).val = (some aIndex, stopA) ∧
                  (boundedUniform other trials n stopA).val = (some bIndex, stopB) := by
                refine ⟨?_, ?_, ?_⟩
                · exact (hagree start le_rfl (by omega)).symm.trans hhold
                · exact hA.2 other (fun i hlo hhi => hagree i (by omega) (by omega))
                · exact hB.2 other (fun i hlo hhi => hagree i (by omega) (by omega))
              -- Selection/classification/weight tests read no tape. At each
              -- successful leaf, the final cursor is stopB or the acceptance
              -- draw's ending cursor, and replayDraws fixes both index draws.
              split at hrun
              · rename_i optionA optionB a b hSelA hSelB
                simp +instances only [Arlib.Computation.Charged.val_bind, erasePaired, insertPaired,
                  Arlib.Computation.Charged.val_opMany] at hrun
                split at hrun
                · have hout := Option.some.inj hrun
                  have hstop : stopB ≤ out.2 := by rw [← hout]
                  refine ⟨hstartB.trans hstop, ?_⟩
                  intro other hagree
                  obtain ⟨hb, hdA, hdB⟩ := replayDraws other hstop hagree
                  simp +instances only [Arlib.Computation.Charged.val_bind, fairBit, successor,
                    Arlib.Computation.Charged.val_op, hb, Bool.false_eq_true, ite_false,
                    hdA, hdB, erasePaired, insertPaired, Arlib.Computation.Charged.val_opMany]
                  simp +instances only [*, Arlib.Computation.Charged.val_bind,
                    Arlib.Computation.Charged.val_pure, Arlib.Computation.Charged.val_opMany]
                · simp +instances only [Arlib.Computation.Charged.val_bind] at hrun
                  split at hrun
                  · rename_i oldWeight newWeight hOld hNew
                    simp +instances only [Arlib.Computation.Charged.val_bind] at hrun
                    by_cases hneed : (ratLess (ratDiv newWeight oldWeight).val 1).val = true
                    · rw [if_pos hneed] at hrun
                      simp +instances only [Arlib.Computation.Charged.val_bind,
                        ratDiv, rationalDenominator, rationalNumerator,
                        Arlib.Computation.Charged.val_opMany] at hrun
                      cases hdrawC : (boundedUniform tape trials
                          (newWeight / oldWeight).den stopB).val with
                      | mk choiceC stopC =>
                        cases choiceC with
                        | none =>
                          simp +instances only [hdrawC, Arlib.Computation.Charged.val_bind,
                            Arlib.Computation.Charged.val_pure] at hrun
                          contradiction
                        | some value =>
                          simp +instances only [hdrawC, Arlib.Computation.Charged.val_bind] at hrun
                          have hC := boundedUniform_interval_replay trials
                            (newWeight / oldWeight).den stopB tape
                          simp +instances only [hdrawC] at hC
                          split at hrun
                          all_goals
                            have hout := Option.some.inj hrun
                            have hstop : stopC = out.2 := by rw [← hout]
                            have hstopB : stopB ≤ out.2 := hstop ▸ hC.1
                            refine ⟨hstartB.trans hstopB, ?_⟩
                            intro other hagree
                            obtain ⟨hb, hdA, hdB⟩ := replayDraws other hstopB hagree
                            have hdC := hC.2 other (fun i hlo hhi => hagree i
                              (hstartB.trans hlo) (by omega))
                            simp +instances only [Arlib.Computation.Charged.val_bind, fairBit, successor,
                              Arlib.Computation.Charged.val_op, hb, Bool.false_eq_true, ite_false,
                              hdA, hdB, erasePaired, insertPaired]
                            simp +instances only [*, Arlib.Computation.Charged.val_bind,
                              Arlib.Computation.Charged.val_opMany]
                            simp +instances only [*, Arlib.Computation.Charged.val_bind,
                              Arlib.Computation.Charged.val_opMany, Arlib.Computation.Charged.val_op,
                              ratDiv, rationalDenominator, rationalNumerator]
                            simp +instances only [*, Arlib.Computation.Charged.val_bind,
                              Arlib.Computation.Charged.val_opMany, Arlib.Computation.Charged.val_pure,
                              Bool.false_eq_true, ite_true, ite_false]
                            simpa only [← hstop] using congrArg some hout
                    · rw [if_neg hneed] at hrun
                      have hout := Option.some.inj hrun
                      have hstop : stopB ≤ out.2 := by rw [← hout]
                      refine ⟨hstartB.trans hstop, ?_⟩
                      intro other hagree
                      obtain ⟨hb, hdA, hdB⟩ := replayDraws other hstop hagree
                      simp +instances only [Arlib.Computation.Charged.val_bind, fairBit, successor,
                        Arlib.Computation.Charged.val_op, hb, Bool.false_eq_true, ite_false,
                        hdA, hdB, erasePaired, insertPaired]
                      simp +instances only [*, Arlib.Computation.Charged.val_bind,
                        Arlib.Computation.Charged.val_opMany, Arlib.Computation.Charged.val_pure]
                      simp only [Bool.false_eq_true, ite_false, Arlib.Computation.Charged.val_pure]
                  · cases hrun
              · simp +instances only [Arlib.Computation.Charged.val_pure] at hrun
                contradiction
