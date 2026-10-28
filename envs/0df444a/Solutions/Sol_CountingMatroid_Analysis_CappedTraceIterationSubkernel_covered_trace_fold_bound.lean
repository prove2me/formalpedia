-- Prove2me | solution 1 for CountingMatroid.Analysis.CappedTraceIterationSubkernel.covered_trace_fold_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:17:25.761522+00:00
-- url     : https://prove2.me/submissions/d4223220-1ab6-41eb-9a02-e54a6b2f33a7

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
import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_Dirichlet
import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_HittingTime
import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_PotentialDecay
import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_SpectralGap
import Definitions.Def_CountingMatroidSupport_Probability_Bilinear
import Definitions.Def_CountingMatroidSupport_Probability_FinDist
import Definitions.Def_CountingMatroidSupport_Probability_FinDistFunctional
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhase
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhaseHistory
import Definitions.Def_CountingMatroid_Analysis_BoundedUniformReplay
import Definitions.Def_CountingMatroid_Analysis_CappedTraceIterationSubkernel
import Definitions.Def_CountingMatroid_Analysis_CappedTraceReturnSubkernel
import Definitions.Def_CountingMatroid_Analysis_ChainStepIntervalReplay
import Definitions.Def_CountingMatroid_Analysis_FiniteStoppedFiberMass
import Definitions.Def_CountingMatroid_Analysis_FirstPhaseFailure
import Definitions.Def_CountingMatroid_Analysis_PositiveTimeTraceKernel
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
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Data.BitVec
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.List.Basic
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
import Mathlib.Topology.Order.MonotoneConvergence
import Theorems.Thm_CountingMatroid_Analysis_CappedTraceReturnSubkernel_covered_return_scan_bound
import Theorems.Thm_CountingMatroid_Analysis_CappedTraceReturnSubkernel_trace_return_scan_eq
import Theorems.Thm_CountingMatroid_Analysis_ChainStepIntervalReplay_foldl_successReplay
import Theorems.Thm_CountingMatroid_Analysis_FiniteStoppedKernelBind_stopped_kernel_bind_covered_bound
import Theorems.Thm_CountingMatroid_Analysis_RestartPhaseTransversal_traceReturn_transversal
import Theorems.Thm_CountingMatroid_Analysis_TraceReturnIntervalReplay_traceReturn_success_interval

namespace CountingMatroid.Analysis.RestartPhaseTransversal
end CountingMatroid.Analysis.RestartPhaseTransversal
namespace CountingMatroid.Analysis.RestartPhaseIntervalReplay
end CountingMatroid.Analysis.RestartPhaseIntervalReplay
namespace CountingMatroid.Analysis.InitialRestartLaw
end CountingMatroid.Analysis.InitialRestartLaw
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
namespace CountingMatroid.Analysis.TraceReturnIntervalReplay
end CountingMatroid.Analysis.TraceReturnIntervalReplay
namespace CountingMatroid.Analysis.FiniteStoppedKernelBind
end CountingMatroid.Analysis.FiniteStoppedKernelBind
namespace Arlib.MarkovChains
end Arlib.MarkovChains
namespace Arlib.MarkovChains.FinChain
end Arlib.MarkovChains.FinChain
namespace Arlib.MarkovChains.FinKernel
end Arlib.MarkovChains.FinKernel
namespace Arlib.Probability
end Arlib.Probability
namespace Arlib.Probability.FinDist
end Arlib.Probability.FinDist
namespace Arlib.Probability.FinKernel
end Arlib.Probability.FinKernel
namespace CountingMatroid.Analysis.ChainStepNoninvalid
end CountingMatroid.Analysis.ChainStepNoninvalid
section


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-! Finite uniform tape disintegration at a successful fixed endpoint cursor. -/
namespace CountingMatroid.Analysis.FiniteStoppedFiberMass















/-- INTERNAL: Inclusion of finite-tape events increases their mass. -/
theorem fairMass_mono (head : List Bool) (t : ℕ) (E F : (ℕ → Bool) → Prop)
    (h : ∀ bits : List.Vector Bool t,
      E (finiteTape (head ++ bits.val)) → F (finiteTape (head ++ bits.val))) :
    fairMass head t E ≤ fairMass head t F := by
  classical
  apply Finset.sum_le_sum
  intro bits _
  by_cases he : E (finiteTape (head ++ bits.val))
  · simp only [he, h bits he, if_true, le_refl]
  · simp only [he, if_false]
    split_ifs <;> positivity





end CountingMatroid.Analysis.FiniteStoppedFiberMass

end

section


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-! The successful finite-tape sublaw of an operational positive-time return.
The recursive scan keeps the global attempt counter and aborts explicitly. -/
namespace CountingMatroid.Analysis.CappedTraceReturnSubkernel
open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.FiniteStoppedFiberMass
open CountingMatroid.Analysis.PositiveTimeTraceKernel













/-- INTERNAL: The actual globally capped positive-time return is dominated
by a reference return granted the whole cap afresh.
TEXLINE: main.tex:1163-1176,1392-1421 -/
theorem covered_trace_return_bound {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (s : AnnealingSchedule) (q : ℚ) (w : Multipliers n)
    (P : Arlib.MarkovChains.FinChain (PairedSet n))
    (hstep : ∀ (head : List Bool) (t : ℕ) (x y : PairedSet n),
      (classifyState x).val ≠ .invalid →
      fairMass head t (fun tape => ∃ stop, stop ≤ head.length + t ∧
        (chainStep r o₁ o₂ tape s.drawTrials q w x head.length).val = some (y, stop)) ≤ P x y)
    (head : List Bool) (t : ℕ) (current : RestartCursor n)
    (hcursor : current.bitCursor = head.length)
    (hvalid : (classifyState current.state).val ≠ .invalid) (target : PairedSet n) :
    fairMass head t (fun tape => ∃ out : RestartCursor n,
      out.bitCursor ≤ head.length + t ∧
      (traceReturn r o₁ o₂ tape s q w current).val = some out ∧ out.state = target) ≤
      (returnWithin P (Finset.univ.filter
        (fun x => (classifyState x).val = .transversal)) s.restartCap).entry current.state target := by
  simp_rw [trace_return_scan_eq]
  exact covered_return_scan_bound r o₁ o₂ s q w P hstep s.restartCap
    head t current hcursor hvalid target

end CountingMatroid.Analysis.CappedTraceReturnSubkernel

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · proved · recursive globally capped return scan equals traceReturn; induction on its horizon composes the covered one-step comparison with finite stopped-prefix bounds.
-/

end

section


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-! Compose covered operational positive-time returns while retaining their
shared attempt counter and the actual cursor between returns. -/
namespace CountingMatroid.Analysis.CappedTraceIterationSubkernel
open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.FiniteStoppedFiberMass
open CountingMatroid.Analysis.PositiveTimeTraceKernel



/-- INTERNAL: Aborted trace folds remain aborted. -/
theorem trace_fold_none {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (q : ℚ) (w : Multipliers n)
    (xs : List ℕ) : traceFold r o₁ o₂ tape s q w xs none = none := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simpa only [traceFold, Arlib.Computation.Charged.val_foldl_cons,
      Arlib.Computation.Charged.val_pure] using ih

/-- INTERNAL: Split off one actual positive-time return, preserving its cursor. -/
theorem trace_fold_cons {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (q : ℚ) (w : Multipliers n)
    (a : ℕ) (xs : List ℕ) (current : RestartCursor n) :
    traceFold r o₁ o₂ tape s q w (a::xs) (some current) =
      ((traceReturn r o₁ o₂ tape s q w current).val).bind
        (fun next => traceFold r o₁ o₂ tape s q w xs (some next)) := by
  unfold traceFold
  rw [Arlib.Computation.Charged.val_foldl_cons]
  cases h : (traceReturn r o₁ o₂ tape s q w current).val with
  | none => exact trace_fold_none r o₁ o₂ tape s q w xs
  | some next => rfl

/-- INTERNAL: A successful trace fold replays exactly its consumed interval.
TEXLINE: main.tex:1163-1176,1392-1421 -/
theorem trace_fold_success_interval {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (s : AnnealingSchedule) (q : ℚ) (w : Multipliers n) (xs : List ℕ)
    (current : RestartCursor n) :
    ChainStepIntervalReplay.SuccessReplay
      (fun tape => traceFold r o₁ o₂ tape s q w xs (some current))
      RestartCursor.bitCursor current.bitCursor := by
  apply ChainStepIntervalReplay.foldl_successReplay
  · intro tape a
    rfl
  · intro acc a
    exact TraceReturnIntervalReplay.traceReturn_success_interval r o₁ o₂ s q w acc



end CountingMatroid.Analysis.CappedTraceIterationSubkernel

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · proved · absorbing-option return folds replay consumed intervals and are dominated by ideal return iteration while preserving shared attempts and abort mass.
-/

end
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-! Compose covered operational positive-time returns while retaining their
shared attempt counter and the actual cursor between returns. -/
namespace CountingMatroid.Analysis.CappedTraceIterationSubkernel
end CountingMatroid.Analysis.CappedTraceIterationSubkernel
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.CappedTraceIterationSubkernel
open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.FiniteStoppedFiberMass
open CountingMatroid.Analysis.PositiveTimeTraceKernel

/-- INTERNAL: Iterated covered actual returns are dominated by iterated ideal
returns, each of which is granted the full restart cap.
TEXLINE: main.tex:1163-1176,1392-1421 -/
theorem solution {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (s : AnnealingSchedule) (q : ℚ) (w : Multipliers n)
    (P : Arlib.MarkovChains.FinChain (PairedSet n))
    (hstep : ∀ (head : List Bool) (t : ℕ) (x y : PairedSet n),
      (classifyState x).val ≠ .invalid →
      fairMass head t (fun tape => ∃ stop, stop ≤ head.length + t ∧
        (chainStep r o₁ o₂ tape s.drawTrials q w x head.length).val = some (y, stop)) ≤ P x y)
    (xs : List ℕ) (head : List Bool) (t : ℕ) (current : RestartCursor n)
    (hcursor : current.bitCursor = head.length)
    (hvalid : (classifyState current.state).val ≠ .invalid) (target : PairedSet n) :
    fairMass head t (fun tape => ∃ out : RestartCursor n,
      out.bitCursor ≤ head.length+t ∧
      traceFold r o₁ o₂ tape s q w xs (some current) = some out ∧ out.state = target) ≤
      (iterate (returnWithin P (Finset.univ.filter
        (fun x => (classifyState x).val = .transversal)) s.restartCap) xs.length).entry
        current.state target := by
  classical
  let K := returnWithin P (Finset.univ.filter
    (fun x : PairedSet n => (classifyState x).val = .transversal)) s.restartCap
  induction xs generalizing head t current with
  | nil =>
    change _ ≤ if current.state = target then 1 else 0
    by_cases hs : current.state = target
    · simp only [hs, if_true]
      unfold fairMass
      calc
        _ ≤ ∑ _ : List.Vector Bool t, 1 / (2 : ℝ)^t := by
          apply Finset.sum_le_sum
          intro bits _
          split_ifs
          · exact le_rfl
          · positivity
        _ = 1 := by simp [card_vector]
    · simp only [hs, if_false]
      have he : ∀ tape, ¬ ∃ out : RestartCursor n,
          out.bitCursor ≤ head.length+t ∧
          traceFold r o₁ o₂ tape s q w [] (some current) = some out ∧ out.state = target := by
        intro tape
        rintro ⟨out, _, hr, ht⟩
        have heq : current = out := Option.some.inj hr
        exact hs (heq ▸ ht)
      simp only [fairMass, he, if_false, Finset.sum_const_zero, le_refl]
  | cons a xs ih =>
    let f := fun tape => (traceReturn r o₁ o₂ tape s q w current).val
    let E := fun tape (middle : RestartCursor n) => ∃ out : RestartCursor n,
      out.bitCursor ≤ head.length+t ∧
      traceFold r o₁ o₂ tape s q w xs (some middle) = some out ∧ out.state = target
    have hevent : ∀ bits : List.Vector Bool t,
        (∃ out : RestartCursor n, out.bitCursor ≤ head.length+t ∧
          traceFold r o₁ o₂ (finiteTape (head ++ bits.val)) s q w (a::xs) (some current) =
            some out ∧ out.state = target) →
        ∃ middle, f (finiteTape (head ++ bits.val)) = some middle ∧
          E (finiteTape (head ++ bits.val)) middle := by
      intro bits
      rintro ⟨out, hc, hr, ht⟩
      rw [trace_fold_cons] at hr
      obtain ⟨middle, hm, htail⟩ := Option.bind_eq_some_iff.mp hr
      exact ⟨middle, hm, out, hc, htail, ht⟩
    have hf : ChainStepIntervalReplay.SuccessReplay f RestartCursor.bitCursor head.length := by
      rw [← hcursor]
      exact TraceReturnIntervalReplay.traceReturn_success_interval r o₁ o₂ s q w current
    have hbound := FiniteStoppedKernelBind.stopped_kernel_bind_covered_bound
      head t f RestartCursor.bitCursor RestartCursor.state hf E
      (fun x => (iterate K xs.length).entry x target)
      (fun x => (iterate K xs.length).nonneg x target) (by
        intro bits middle _ hE
        obtain ⟨out, hc, hr, _⟩ := hE
        exact (trace_fold_success_interval r o₁ o₂ s q w xs middle _ out hr).1.trans hc)
      (by
        intro middle hstart hstop pref hm
        have hlen : (head ++ pref.val).length = middle.bitCursor := by
          simp only [List.length_append, pref.2]
          omega
        have hbudget : (head ++ pref.val).length + (t-(middle.bitCursor-head.length)) =
            head.length+t := by rw [hlen]; omega
        have hv : (classifyState middle.state).val ≠ .invalid := by
          have ht := RestartPhaseTransversal.traceReturn_transversal r o₁ o₂
            (finiteTape (head ++ pref.val)) s q w current middle hm
          rw [ht]
          intro h
          cases h
        have hi := ih (head ++ pref.val) (t-(middle.bitCursor-head.length)) middle
          hlen.symm hv
        have heq : fairMass (head ++ pref.val) (t-(middle.bitCursor-head.length))
            (fun tape => E tape middle) =
            fairMass (head ++ pref.val) (t-(middle.bitCursor-head.length)) (fun tape =>
              ∃ out : RestartCursor n,
                out.bitCursor ≤ (head ++ pref.val).length + (t-(middle.bitCursor-head.length)) ∧
                traceFold r o₁ o₂ tape s q w xs (some middle) = some out ∧ out.state = target) := by
          unfold fairMass
          apply Finset.sum_congr rfl
          intro bits _
          simp only [E, hbudget]
        rw [heq]
        exact hi)
    calc
      _ ≤ fairMass head t (fun tape => ∃ middle, f tape = some middle ∧ E tape middle) :=
        fairMass_mono head t _ _ hevent
      _ ≤ ∑ x : PairedSet n, fairMass head t (fun tape => ∃ middle, f tape = some middle ∧
          middle.bitCursor ≤ head.length+t ∧ middle.state = x) *
          (iterate K xs.length).entry x target := hbound
      _ ≤ ∑ x : PairedSet n, K.entry current.state x * (iterate K xs.length).entry x target := by
        apply Finset.sum_le_sum
        intro x _
        apply mul_le_mul_of_nonneg_right _ ((iterate K xs.length).nonneg x target)
        have hb := CappedTraceReturnSubkernel.covered_trace_return_bound r o₁ o₂ s q w P hstep
          head t current hcursor hvalid x
        have heq : fairMass head t (fun tape => ∃ middle, f tape = some middle ∧
            middle.bitCursor ≤ head.length+t ∧ middle.state = x) =
            fairMass head t (fun tape => ∃ out : RestartCursor n,
              out.bitCursor ≤ head.length+t ∧
              (traceReturn r o₁ o₂ tape s q w current).val = some out ∧ out.state = x) := by
          unfold fairMass
          apply Finset.sum_congr rfl
          intro bits _
          congr 1
          exact propext (by
            constructor <;> rintro ⟨out, h₁, h₂, h₃⟩ <;> exact ⟨out,h₂,h₁,h₃⟩)
        rw [heq]
        exact hb
      _ = _ := rfl
