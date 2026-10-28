-- Prove2me | solution 1 for CountingMatroid.Analysis.RestartDrawProbeBitBound.restart_draw_probe_bit_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:02:39.860083+00:00
-- url     : https://prove2.me/submissions/ffe118a0-fab2-4df6-a767-52af57d971d7

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
import Definitions.Def_CountingMatroid_Analysis_AnnealingPartitionDrift
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhase
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhaseHistory
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhaseWork
import Definitions.Def_CountingMatroid_Analysis_BoundedUniformAbortMass
import Definitions.Def_CountingMatroid_Analysis_BoundedUniformReplay
import Definitions.Def_CountingMatroid_Analysis_ChainDrawSiteReplay
import Definitions.Def_CountingMatroid_Analysis_ChainStepIntervalReplay
import Definitions.Def_CountingMatroid_Analysis_DefectPartitionPositive
import Definitions.Def_CountingMatroid_Analysis_EmpiricalPhaseCertificate
import Definitions.Def_CountingMatroid_Analysis_EstimateMedianResource
import Definitions.Def_CountingMatroid_Analysis_FinishPhaseEmpiricalUpdate
import Definitions.Def_CountingMatroid_Analysis_FinishPhaseWork
import Definitions.Def_CountingMatroid_Analysis_FirstPhaseFailure
import Definitions.Def_CountingMatroid_Analysis_InitialMultipliersGood
import Definitions.Def_CountingMatroid_Analysis_ObservePhaseWork
import Definitions.Def_CountingMatroid_Analysis_PhaseChainWork
import Definitions.Def_CountingMatroid_Analysis_PhaseMeanCertificate
import Definitions.Def_CountingMatroid_Analysis_PhaseObservationExperiment
import Definitions.Def_CountingMatroid_Analysis_PhaseResourcePrimitives
import Definitions.Def_CountingMatroid_Analysis_RationalHeight
import Definitions.Def_CountingMatroid_Analysis_RelativeObservationBounds
import Definitions.Def_CountingMatroid_Analysis_RestartAttemptAccounting
import Definitions.Def_CountingMatroid_Analysis_RestartDrawProbe
import Definitions.Def_CountingMatroid_Analysis_RestartDrawProbeBitBound
import Definitions.Def_CountingMatroid_Analysis_ScheduleConfidence
import Definitions.Def_CountingMatroid_Analysis_ScheduleOpeningCost
import Definitions.Def_CountingMatroid_Analysis_ScheduleThermalSetupCost
import Definitions.Def_CountingMatroid_Analysis_StationaryMeanIdentities
import Definitions.Def_CountingMatroid_Analysis_TransversalClassPartition
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
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Data.BitVec
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Induction
import Mathlib.Data.List.Infix
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sort
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Data.Set.Finite.List
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
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
import Theorems.Thm_CountingMatroid_Analysis_BoundedRunResourceEnvelope_ratPower_binary_length_le
import Theorems.Thm_CountingMatroid_Analysis_ChainStepBitBound_chain_draw_site_bit_bound
import Theorems.Thm_CountingMatroid_Analysis_ChainStepBitBound_chain_step_bit_bound

namespace CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
end CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
namespace CountingMatroid.Analysis.LeastHalvingsCost
end CountingMatroid.Analysis.LeastHalvingsCost
namespace CountingMatroid.Analysis
end CountingMatroid.Analysis
namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
namespace CountingMatroid.Analysis.ChainStepBitBound
end CountingMatroid.Analysis.ChainStepBitBound
namespace CountingMatroid.Analysis.FiniteObservationMarkov
end CountingMatroid.Analysis.FiniteObservationMarkov
namespace CountingMatroid.Analysis.FiniteTapePrefixBound
end CountingMatroid.Analysis.FiniteTapePrefixBound
namespace CountingMatroid.Analysis.InitialRestartLaw
end CountingMatroid.Analysis.InitialRestartLaw
namespace CountingMatroid.Interface
end CountingMatroid.Interface
namespace CountingMatroid.Analysis.TransversalRankBridge
end CountingMatroid.Analysis.TransversalRankBridge
namespace CountingMatroid.Analysis.GreedyRankCorrect
end CountingMatroid.Analysis.GreedyRankCorrect
namespace CountingMatroid.Analysis.SuccessfulPrefixAbortBound
end CountingMatroid.Analysis.SuccessfulPrefixAbortBound
namespace CountingMatroid.Analysis.BoundedRunResourceEnvelope
end CountingMatroid.Analysis.BoundedRunResourceEnvelope
namespace CountingMatroid.Analysis.BoundedRunOtherSteps
end CountingMatroid.Analysis.BoundedRunOtherSteps
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
section


set_option autoImplicit false

namespace CountingMatroid.Analysis.BoundedRunResourceEnvelope

open CountingMatroid.Model
open CountingMatroid.Model.Operations
open CountingMatroid.Model.Subroutines
open CountingMatroid.Analysis.RationalHeight



/-- INTERNAL: A charged finite loop preserves any invariant preserved by its body. -/
theorem chargedFold_preserves {ι β : Type} (P : β → Prop)
    (f : β → ι → Arlib.Computation.Charged Op Cell β)
    (hf : ∀ b i, P b → P (f b i).val) (l : List ι) (b : β) (hb : P b) :
    P (Arlib.Computation.Charged.foldl f l b).val := by
  induction l generalizing b with
  | nil => simpa using hb
  | cons i xs ih =>
      rw [Arlib.Computation.Charged.val_foldl_cons]
      exact ih _ (hf b i hb)





















end CountingMatroid.Analysis.BoundedRunResourceEnvelope

end

section


set_option autoImplicit false

/-!
The phase-zero restart is exactly a fresh uniform transversal, with no return
excursion or restart-cap failure. The lemmas below retain the actual bit cursor
and the finite-tape suffix, rather than supplying a new random source.
-/

namespace CountingMatroid.Analysis.InitialRestartLaw

open CountingMatroid.Model CountingMatroid.Model.Operations CountingMatroid.Program

/-- INTERNAL: Split a charged fold's value at a list boundary. -/
private theorem foldl_append_value {α β : Type}
    (f : β → α → Arlib.Computation.Charged Op Cell β)
    (xs ys : List α) (initial : β) :
    (Arlib.Computation.Charged.foldl f (xs ++ ys) initial).val =
      (Arlib.Computation.Charged.foldl f ys
        (Arlib.Computation.Charged.foldl f xs initial).val).val := by
  induction xs generalizing initial with
  | nil => rfl
  | cons x xs ih =>
      simpa only [List.cons_append, Arlib.Computation.Charged.val_foldl_cons]
        using ih (f initial x).val

/-- INTERNAL: Evaluate the fresh-bit scan on an indexed list, including its
cursor movement and all elements inserted into the actual paired set.
TEXLINE: main.tex:1163-1176 -/
private theorem fresh_scan_value {n : ℕ} (tape : ℕ → Bool) (k : ℕ)
    (indices : Fin k → Fin n) (state : PairedSet n) (cursor : ℕ) :
    (Arlib.Computation.Charged.foldl (fun acc i => do
      let bit ← fairBit tape acc.2
      let state ← insertPaired acc.1 (i, bit)
      let next ← successor acc.2
      pure (state, next)) (List.ofFn indices) (state, cursor)).val =
      (state ∪ Finset.univ.image (fun i : Fin k => (indices i, tape (cursor + i))),
        cursor + k) := by
  induction k generalizing state cursor with
  | zero => simp
  | succ k ih =>
      rw [List.ofFn_succ', List.concat_eq_append]
      change (Arlib.Computation.Charged.foldl _
        (List.ofFn (fun i : Fin k => indices i.castSucc) ++ [indices (Fin.last k)])
          (state, cursor)).val = _
      rw [foldl_append_value, ih]
      simp only [Arlib.Computation.Charged.val_foldl_cons,
        Arlib.Computation.Charged.val_foldl_nil, Arlib.Computation.Charged.val_bind,
        fairBit, insertPaired, successor, Arlib.Computation.Charged.val_op,
        Arlib.Computation.Charged.val_opMany, Arlib.Computation.Charged.val_pure]
      congr 1
      · rw [Fin.univ_castSuccEmb, Finset.cons_eq_insert, Finset.image_insert,
          Finset.map_eq_image, Finset.image_image]
        simp only [Fin.coe_castSuccEmb, Fin.val_last]
        simp only [Finset.union_insert]
        rfl

/-- PAPER: main.tex:1163-1176
A fresh restart reads precisely the next n bits and selects one element from
each pair. This equality also identifies the law when those bits are fair. -/
theorem freshTransversal_value (n : ℕ) (tape : ℕ → Bool) (cursor : ℕ) :
    (freshTransversal n tape cursor).val =
      (Finset.univ.image (fun i : Fin n => (i, tape (cursor + i))), cursor + n) := by
  simpa only [freshTransversal, ← List.ofFn_id, Finset.empty_union, id_eq] using
    fresh_scan_value tape n id (∅ : PairedSet n) cursor




















end CountingMatroid.Analysis.InitialRestartLaw

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r19 · proved · evaluated the actual fresh-bit scan and phase-zero restart,
  split finite tapes into equally weighted prefixes and observation suffixes,
  and derived the exact initial certificate-failure mass identity. No chain
  concentration bound, extra hypothesis, or unproved declaration introduced.
-/

end

section


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-!
Quantitative bit-cursor coverage for a single probed restart ordinal,
retained even when the probed attempt later aborts. The argument mirrors
the chain/restart bit-budget invariant used for a completed restart, but
tracks the first captured draw descriptor instead of the loop's final
output.
-/
namespace CountingMatroid.Analysis.RestartDrawProbeBitBound

open CountingMatroid.Model CountingMatroid.Model.Operations CountingMatroid.Program
open CountingMatroid.Analysis.RestartAttemptAccounting
open CountingMatroid.Analysis.RestartDrawProbe
open CountingMatroid.Analysis.ObservationRoundDrawSites
open CountingMatroid.Analysis.ChainStepBitBound
open CountingMatroid.Analysis.BoundedRunResourceEnvelope



/-- INTERNAL: Preserve an invariant across a charged early-break loop. -/
private theorem foldWhile_inv {α β : Type} (P : β → Prop)
    (f : β → α → Arlib.Computation.Charged Op Cell (Option β))
    (hf : ∀ b a next, P b → (f b a).val = some next → P next)
    (xs : List α) (b : β) (hb : P b) :
    P (Arlib.Computation.Charged.foldlWhile f xs b).val := by
  induction xs generalizing b with
  | nil => exact hb
  | cons a xs ih =>
      cases he : (f b a).val with
      | none =>
          simp only [Arlib.Computation.Charged.val] at he ⊢
          simpa only [Arlib.Computation.Charged.foldlWhile, he] using hb
      | some next =>
          have hn := ih next (hf b a next hb he)
          simp only [Arlib.Computation.Charged.val] at he hn ⊢
          simpa only [Arlib.Computation.Charged.foldlWhile, he] using hn

/-- INTERNAL: A list-indexed charged fold preserves an invariant using only
the list membership of the index actually consumed. -/
private theorem fold_mem_inv {α β : Type} (P : β → Prop)
    (f : β → α → Arlib.Computation.Charged Op Cell β) (xs : List α)
    (hf : ∀ b a, a ∈ xs → P b → P (f b a).val) (b : β) (hb : P b) :
    P (Arlib.Computation.Charged.foldl f xs b).val := by
  induction xs generalizing b with
  | nil => exact hb
  | cons a xs ih =>
      rw [Arlib.Computation.Charged.val_foldl_cons]
      exact ih (fun b i hi => hf b i (List.mem_cons_of_mem a hi))
        _ (hf b a List.mem_cons_self hb)

/-- INTERNAL: One probed body call extends the joint invariant, using the
original chain-step and chain-draw-site bit bounds. -/
private theorem probedBody_inv {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (q : ℚ) (w : Multipliers n)
    (base K : ℕ) (hq : binaryRatLength 1 + n * binaryRatLength q ≤ K)
    (hw : ∀ i, binaryRatLength (w i) ≤ K) (ordinal : ℕ) (draw : Fin 3)
    (acc : ((Option (RestartCursor n) × Bool) × ℕ) × Option (ℕ × ℕ))
    (hacc : ProbeInv s base K (1 + 3 * s.drawTrials * (4 * K + n + 1))
      acc.1.1.1 acc.1.2 acc.2)
    (next : ((Option (RestartCursor n) × Bool) × ℕ) × Option (ℕ × ℕ))
    (he : (probedBody r o₁ o₂ tape s q w ordinal draw acc).val = some next) :
    ProbeInv s base K (1 + 3 * s.drawTrials * (4 * K + n + 1))
      next.1.1.1 next.1.2 next.2 := by
  obtain ⟨⟨⟨cur0, stop0⟩, count0⟩, obs0⟩ := acc
  obtain ⟨hcur0, hobs0⟩ := hacc
  simp only [probedBody, Arlib.Computation.Charged.val_bind, Arlib.Computation.Charged.val_pure,
    Option.map_eq_some_iff] at he
  obtain ⟨result, hresult, hnext⟩ := he
  have hnext1 : next.1 = result := congrArg Prod.fst hnext.symm
  have hnext2 : next.2 =
      obs0.or (bodySite r o₁ o₂ tape s q w ordinal draw ((cur0, stop0), count0)) :=
    congrArg Prod.snd hnext.symm
  refine ⟨?_, ?_⟩
  · intro current hcurrent
    rw [hnext1] at hcurrent
    unfold countedBody at hresult
    simp only [Arlib.Computation.Charged.val_bind, Arlib.Computation.Charged.val_pure,
      Option.map_eq_some_iff] at hresult
    obtain ⟨tbresult, htb, hre⟩ := hresult
    have hre1 : result.1 = tbresult := congrArg Prod.fst hre.symm
    have hre2 : result.2 = count0 + attemptIncrement s (cur0, stop0) := congrArg Prod.snd hre.symm
    rw [hre1] at hcurrent
    unfold traceBody at htb
    split at htb
    · simp only [Arlib.Computation.Charged.val_pure] at htb
      cases htb
    · rename_i hstop
      cases hcc : cur0 with
      | none => simp only [hcc, Arlib.Computation.Charged.val_pure] at htb; cases htb
      | some current0 =>
          simp only [hcc, Arlib.Computation.Charged.val_bind, lessThan,
            Arlib.Computation.Charged.val_op] at htb
          split at htb
          · rename_i hallowed
            have hlt : current0.attempts < s.restartCap := of_decide_eq_true hallowed
            simp only [Arlib.Computation.Charged.val_bind] at htb
            cases hchain : (chainStep r o₁ o₂ tape s.drawTrials q w
                current0.state current0.bitCursor).val with
            | none =>
                simp only [hchain, Arlib.Computation.Charged.val_pure,
                  Option.some.injEq] at htb
                rw [← htb] at hcurrent
                cases hcurrent
            | some attempted =>
                simp only [hchain, Arlib.Computation.Charged.val_bind, successor,
                  Arlib.Computation.Charged.val_op] at htb
                have hbit := chain_step_bit_bound r o₁ o₂ tape s.drawTrials q w
                  current0.state current0.bitCursor K hq hw attempted hchain
                obtain ⟨hattempt0, hbit0, hcount0⟩ := hcur0 current0 hcc
                have hcount0' : count0 = current0.attempts := hcount0
                have hinc : attemptIncrement s (cur0, stop0) = 1 := by
                  unfold attemptIncrement
                  rw [if_neg hstop, hcc]
                  exact if_pos hlt
                have hnext12 : next.1.2 = result.2 := congrArg Prod.snd hnext1
                cases attempted with
                | mk state stop =>
                    cases hk : (classifyState state).val <;>
                      simp only [hk, Arlib.Computation.Charged.val_bind,
                        Arlib.Computation.Charged.val_pure, Option.some.injEq] at htb <;>
                      rw [← htb] at hcurrent <;> cases hcurrent <;> dsimp only <;>
                      refine ⟨by omega, by
                        have hC : current0.attempts * (1 + 3 * s.drawTrials * (4 * K + n + 1))
                            + (1 + 3 * s.drawTrials * (4 * K + n + 1)) =
                            (current0.attempts + 1) *
                              (1 + 3 * s.drawTrials * (4 * K + n + 1)) := by ring
                        omega, by omega⟩
          · simp only [Arlib.Computation.Charged.val_pure, Option.some.injEq] at htb
            rw [← htb] at hcurrent
            cases hcurrent
  · intro d hd
    rw [hnext2] at hd
    cases ho : obs0 with
    | some old =>
        simp only [ho, Option.some_or, Option.some.injEq] at hd
        exact hobs0 d (by rw [ho, hd])
    | none =>
        simp only [ho, Option.none_or] at hd
        unfold bodySite at hd
        split at hd
        · cases hd
        · cases hcc : cur0 with
          | none => simp only [hcc] at hd; cases hd
          | some current0 =>
              simp only [hcc] at hd
              split at hd
              · rename_i hcond
                obtain ⟨hlt, hcount⟩ := hcond
                obtain ⟨hattempt0, hbit0, hcount0⟩ := hcur0 current0 hcc
                have hchain := chain_draw_site_bit_bound r o₁ o₂ tape s q w
                  current0.state current0.bitCursor K hq hw draw d hd
                have hCeq : current0.attempts * (1 + 3 * s.drawTrials * (4 * K + n + 1))
                    + (1 + 3 * s.drawTrials * (4 * K + n + 1)) =
                    (current0.attempts + 1) * (1 + 3 * s.drawTrials * (4 * K + n + 1)) := by
                  ring
                have hCle : (current0.attempts + 1) *
                    (1 + 3 * s.drawTrials * (4 * K + n + 1)) ≤
                    s.restartCap * (1 + 3 * s.drawTrials * (4 * K + n + 1)) :=
                  Nat.mul_le_mul_right _ (by omega)
                omega
              · cases hd

/-- INTERNAL: The joint invariant survives a full capped return scan. -/
private theorem probedReturn_inv {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (q : ℚ) (w : Multipliers n)
    (base K : ℕ) (hq : binaryRatLength 1 + n * binaryRatLength q ≤ K)
    (hw : ∀ i, binaryRatLength (w i) ≤ K) (ordinal : ℕ) (draw : Fin 3)
    (start : RestartCursor n) (count : ℕ) (observed : Option (ℕ × ℕ))
    (hstart : ProbeInv s base K (1 + 3 * s.drawTrials * (4 * K + n + 1))
      (some start) count observed) :
    ProbeInv s base K (1 + 3 * s.drawTrials * (4 * K + n + 1))
      (probedReturn r o₁ o₂ tape s q w ordinal draw start count observed).val.1.1
      (probedReturn r o₁ o₂ tape s q w ordinal draw start count observed).val.1.2
      (probedReturn r o₁ o₂ tape s q w ordinal draw start count observed).val.2 := by
  have hscan := foldWhile_inv
    (fun acc : ((Option (RestartCursor n) × Bool) × ℕ) × Option (ℕ × ℕ) =>
      ProbeInv s base K (1 + 3 * s.drawTrials * (4 * K + n + 1)) acc.1.1.1 acc.1.2 acc.2)
    (fun acc (_ : ℕ) => probedBody r o₁ o₂ tape s q w ordinal draw acc)
    (fun acc _ next ha he => probedBody_inv r o₁ o₂ tape s q w base K hq hw ordinal draw
      acc ha next he)
    (List.range s.restartCap) (((some start, false), count), observed) hstart
  unfold probedReturn
  simp only [Arlib.Computation.Charged.val_bind, Arlib.Computation.Charged.val_pure,
    Arlib.Computation.Charged.repeatWhile]
  split
  · exact hscan
  · exact ⟨fun current hcurrent => by simp at hcurrent, hscan.2⟩

/-- INTERNAL: The joint invariant survives one trace transition. -/
private theorem probedTransition_inv {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (q : ℚ) (w : Multipliers n)
    (base K : ℕ) (hq : binaryRatLength 1 + n * binaryRatLength q ≤ K)
    (hw : ∀ i, binaryRatLength (w i) ≤ K) (ordinal : ℕ) (draw : Fin 3)
    (acc : (Option (RestartCursor n) × ℕ) × Option (ℕ × ℕ))
    (hacc : ProbeInv s base K (1 + 3 * s.drawTrials * (4 * K + n + 1))
      acc.1.1 acc.1.2 acc.2) :
    ProbeInv s base K (1 + 3 * s.drawTrials * (4 * K + n + 1))
      (probedTransition r o₁ o₂ tape s q w ordinal draw acc).val.1.1
      (probedTransition r o₁ o₂ tape s q w ordinal draw acc).val.1.2
      (probedTransition r o₁ o₂ tape s q w ordinal draw acc).val.2 := by
  unfold probedTransition
  cases hc : acc.1.1 with
  | none =>
      simp only [Arlib.Computation.Charged.val_pure]
      exact hacc
  | some current =>
      rw [hc] at hacc
      exact probedReturn_inv r o₁ o₂ tape s q w base K hq hw ordinal draw current acc.1.2 acc.2
        hacc

/-- INTERNAL: The joint invariant survives a fixed-weight stage of trace
transitions. -/
private theorem probedStage_inv {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (tables : LearnedWeights n)
    (base K : ℕ) (ordinal : ℕ) (draw : Fin 3) (index : ℕ)
    (hq : binaryRatLength 1 + n * binaryRatLength (ratPower s.ρ (index + 1)).val ≤ K)
    (hw : ∀ i, binaryRatLength ((learnedWeightRead tables (index + 1) s.L).val i) ≤ K)
    (acc : (Option (RestartCursor n) × ℕ) × Option (ℕ × ℕ))
    (hacc : ProbeInv s base K (1 + 3 * s.drawTrials * (4 * K + n + 1))
      acc.1.1 acc.1.2 acc.2) :
    ProbeInv s base K (1 + 3 * s.drawTrials * (4 * K + n + 1))
      (probedStage r o₁ o₂ tape s tables ordinal draw index acc).val.1.1
      (probedStage r o₁ o₂ tape s tables ordinal draw index acc).val.1.2
      (probedStage r o₁ o₂ tape s tables ordinal draw index acc).val.2 := by
  unfold probedStage
  simp only [Arlib.Computation.Charged.val_bind, successor, ratPower, learnedWeightRead,
    Arlib.Computation.Charged.val_op, Arlib.Computation.Charged.repeatFor]
  exact chargedFold_preserves
    (fun acc : (Option (RestartCursor n) × ℕ) × Option (ℕ × ℕ) =>
      ProbeInv s base K (1 + 3 * s.drawTrials * (4 * K + n + 1)) acc.1.1 acc.1.2 acc.2)
    (fun acc (_ : ℕ) => probedTransition r o₁ o₂ tape s
      (ratPower s.ρ (index + 1)).val (learnedWeightRead tables (index + 1) s.L).val ordinal draw acc)
    (fun acc _ ha => probedTransition_inv r o₁ o₂ tape s _ _ base K hq hw ordinal draw acc ha)
    (List.range s.τ) acc hacc



end CountingMatroid.Analysis.RestartDrawProbeBitBound

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · new · joint attempt/cursor/descriptor invariant propagated
  through the probed-restart fold, giving a shared-budget bound on any
  captured ordinal draw descriptor even on a later abort.
-/

end
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-!
Quantitative bit-cursor coverage for a single probed restart ordinal,
retained even when the probed attempt later aborts. The argument mirrors
the chain/restart bit-budget invariant used for a completed restart, but
tracks the first captured draw descriptor instead of the loop's final
output.
-/
namespace CountingMatroid.Analysis.RestartDrawProbeBitBound
end CountingMatroid.Analysis.RestartDrawProbeBitBound
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.RestartDrawProbeBitBound

open CountingMatroid.Model CountingMatroid.Model.Operations CountingMatroid.Program
open CountingMatroid.Analysis.RestartAttemptAccounting
open CountingMatroid.Analysis.RestartDrawProbe
open CountingMatroid.Analysis.ObservationRoundDrawSites
open CountingMatroid.Analysis.ChainStepBitBound
open CountingMatroid.Analysis.BoundedRunResourceEnvelope

/-- INTERNAL: The complete probed restart has a captured descriptor fitting
the whole restart's shared attempt budget.
TEXLINE: main.tex:1350-1390,1392-1421 -/
theorem solution {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (tables : LearnedWeights n)
    (j cursor K : ℕ) (hj : j ≤ s.L)
    (hq : binaryRatLength 1 + n * (binaryRatLength 1 + s.L * binaryRatLength s.ρ) ≤ K)
    (hw : ∀ phase i, binaryRatLength (tables phase i) ≤ K)
    (ordinal : ℕ) (draw : Fin 3) (d : ℕ × ℕ)
    (h : (probedRestart r o₁ o₂ tape s tables j cursor ordinal draw).val.2 = some d) :
    d.1 + s.drawTrials * ((d.2 - 1).log2 + 1) ≤
      cursor + n + s.restartCap * (1 + 3 * s.drawTrials * (4 * K + n + 1)) := by
  let C := 1 + 3 * s.drawTrials * (4 * K + n + 1)
  have hs : ∀ (acc : (Option (RestartCursor n) × ℕ) × Option (ℕ × ℕ)) (index : ℕ),
      index ∈ List.range j → ProbeInv s (cursor + n) K C acc.1.1 acc.1.2 acc.2 →
      ProbeInv s (cursor + n) K C
        (probedStage r o₁ o₂ tape s tables ordinal draw index acc).val.1.1
        (probedStage r o₁ o₂ tape s tables ordinal draw index acc).val.1.2
        (probedStage r o₁ o₂ tape s tables ordinal draw index acc).val.2 := by
    intro acc index hi hacc
    have hi' : index + 1 ≤ s.L := by
      have := List.mem_range.mp hi
      omega
    have hqj : binaryRatLength 1 + n * binaryRatLength (ratPower s.ρ (index + 1)).val ≤ K := by
      have hl := BoundedRunResourceEnvelope.ratPower_binary_length_le s.ρ (index + 1)
      have hm := Nat.mul_le_mul_right (binaryRatLength s.ρ) hi'
      have hh := Nat.mul_le_mul_left n (hl.trans (Nat.add_le_add_left hm _))
      exact (Nat.add_le_add_left hh _).trans hq
    have hwj : ∀ i, binaryRatLength ((learnedWeightRead tables (index + 1) s.L).val i) ≤ K := by
      simpa only [learnedWeightRead, successor, Arlib.Computation.Charged.val_op,
        Arlib.Computation.Charged.val_opMany] using hw (index + 1)
    exact probedStage_inv r o₁ o₂ tape s tables (cursor + n) K ordinal draw index hqj hwj acc hacc
  let initial : RestartCursor n :=
    ⟨(freshTransversal n tape cursor).val.1, (freshTransversal n tape cursor).val.2, 0⟩
  have hi : ProbeInv s (cursor + n) K C (some initial) 0 none := by
    refine ⟨?_, ?_⟩
    · intro current hcurrent
      cases hcurrent
      simp only [initial, InitialRestartLaw.freshTransversal_value, Nat.zero_mul, Nat.add_zero]
      exact ⟨Nat.zero_le _, le_rfl, trivial⟩
    · intro d' hd'
      cases hd'
  have hf := fold_mem_inv
    (fun acc : (Option (RestartCursor n) × ℕ) × Option (ℕ × ℕ) =>
      ProbeInv s (cursor + n) K C acc.1.1 acc.1.2 acc.2)
    (fun acc index => probedStage r o₁ o₂ tape s tables ordinal draw index acc)
    (List.range j) hs ((some initial, 0), none) hi
  unfold probedRestart at h
  simp only [Arlib.Computation.Charged.val_bind, Arlib.Computation.Charged.val_pure,
    Arlib.Computation.Charged.repeatFor] at h
  have h2 : (Arlib.Computation.Charged.foldl
      (fun acc index => probedStage r o₁ o₂ tape s tables ordinal draw index acc)
      (List.range j) ((some initial, 0), none)).val.2 = some d := h
  exact hf.2 d h2
