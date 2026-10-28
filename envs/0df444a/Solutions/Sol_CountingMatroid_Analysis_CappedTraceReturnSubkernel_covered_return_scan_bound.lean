-- Prove2me | solution 1 for CountingMatroid.Analysis.CappedTraceReturnSubkernel.covered_return_scan_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:13:33.500128+00:00
-- url     : https://prove2.me/submissions/d0c8961e-4139-4819-b270-527fe2a6e897

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
import Definitions.Def_CountingMatroid_Analysis_BoundedUniformReplay
import Definitions.Def_CountingMatroid_Analysis_CappedTraceReturnSubkernel
import Definitions.Def_CountingMatroid_Analysis_ChainStepIntervalReplay
import Definitions.Def_CountingMatroid_Analysis_FiniteStoppedFiberMass
import Definitions.Def_CountingMatroid_Analysis_PositiveTimeTraceKernel
import Definitions.Def_CountingMatroid_Model_Operations
import Definitions.Def_CountingMatroid_Model_Prelude
import Definitions.Def_CountingMatroid_Model_Program
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
import Mathlib.Data.List.Sort
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Basic
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
import Theorems.Thm_CountingMatroid_Analysis_CappedTraceReturnSubkernel_return_scan_success_interval
import Theorems.Thm_CountingMatroid_Analysis_ChainStepIntervalReplay_chainStep_success_interval
import Theorems.Thm_CountingMatroid_Analysis_ChainStepNoninvalid_chainStep_noninvalid
import Theorems.Thm_CountingMatroid_Analysis_FiniteStoppedFiberMass_stopped_next_bound

namespace Arlib.MarkovChains
end Arlib.MarkovChains
namespace Arlib.MarkovChains.FinChain
end Arlib.MarkovChains.FinChain
namespace Arlib.MarkovChains.FinKernel
end Arlib.MarkovChains.FinKernel
namespace Arlib
end Arlib
namespace Arlib.Probability
end Arlib.Probability
namespace Arlib.Probability.FinDist
end Arlib.Probability.FinDist
namespace Arlib.Probability.FinKernel
end Arlib.Probability.FinKernel
namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace CountingMatroid.Analysis.ChainStepNoninvalid
end CountingMatroid.Analysis.ChainStepNoninvalid
section


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-! The successful finite-tape sublaw of an operational positive-time return.
The recursive scan keeps the global attempt counter and aborts explicitly. -/
namespace CountingMatroid.Analysis.CappedTraceReturnSubkernel
open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.FiniteStoppedFiberMass
open CountingMatroid.Analysis.PositiveTimeTraceKernel





/-- INTERNAL: Away from the target, a positive-time return is a zero-time hit.
TEXLINE: main.tex:1163-1176 -/
theorem return_within_eq_hit_off_target {α : Type} [Fintype α] [DecidableEq α]
    (P : Arlib.MarkovChains.FinChain α) (A : Finset α) (k : ℕ)
    (x y : α) (hx : x ∉ A) :
    (returnWithin P A k).entry x y = (hitWithin P A k).entry x y := by
  cases k <;> simp only [returnWithin, hitWithin, targetIdentity, hx, false_and, if_false]









end CountingMatroid.Analysis.CappedTraceReturnSubkernel

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · proved · recursive globally capped return scan equals traceReturn; induction on its horizon composes the covered one-step comparison with finite stopped-prefix bounds.
-/

end
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-! The successful finite-tape sublaw of an operational positive-time return.
The recursive scan keeps the global attempt counter and aborts explicitly. -/
namespace CountingMatroid.Analysis.CappedTraceReturnSubkernel
end CountingMatroid.Analysis.CappedTraceReturnSubkernel
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.CappedTraceReturnSubkernel
open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.FiniteStoppedFiberMass
open CountingMatroid.Analysis.PositiveTimeTraceKernel

/-- INTERNAL: A recursive capped return on a covered finite suffix is dominated
by the corresponding ideal positive-time return subkernel.
TEXLINE: main.tex:1163-1176,1392-1421 -/
theorem solution {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (s : AnnealingSchedule) (q : ℚ) (w : Multipliers n)
    (P : Arlib.MarkovChains.FinChain (PairedSet n))
    (hstep : ∀ (head : List Bool) (t : ℕ) (x y : PairedSet n),
      (classifyState x).val ≠ .invalid →
      fairMass head t (fun tape => ∃ stop, stop ≤ head.length + t ∧
        (chainStep r o₁ o₂ tape s.drawTrials q w x head.length).val = some (y, stop)) ≤ P x y)
    (k : ℕ) (head : List Bool) (t : ℕ) (current : RestartCursor n)
    (hcursor : current.bitCursor = head.length)
    (hvalid : (classifyState current.state).val ≠ .invalid) (target : PairedSet n) :
    fairMass head t (fun tape => ∃ out : RestartCursor n,
      out.bitCursor ≤ head.length + t ∧
      returnScan r o₁ o₂ tape s q w k current = some out ∧ out.state = target) ≤
      (returnWithin P (Finset.univ.filter
        (fun x => (classifyState x).val = .transversal)) k).entry current.state target := by
  classical
  let A := Finset.univ.filter (fun x : PairedSet n => (classifyState x).val = .transversal)
  induction k generalizing head t current with
  | zero => simp only [returnScan, reduceCtorEq, and_false, false_and, exists_false,
      fairMass, if_false, Finset.sum_const_zero, returnWithin, le_refl]
  | succ k ih =>
    by_cases ha : current.attempts < s.restartCap
    · let f := fun tape => (chainStep r o₁ o₂ tape s.drawTrials q w
        current.state head.length).val
      let E := fun tape (a : PairedSet n) stop => ∃ out : RestartCursor n,
        out.bitCursor ≤ head.length + t ∧
        (if (classifyState a).val = .transversal then
          some (RestartCursor.mk a stop (current.attempts + 1)) else
          returnScan r o₁ o₂ tape s q w k ⟨a, stop, current.attempts + 1⟩) = some out ∧
        out.state = target
      have hevent : ∀ bits : List.Vector Bool t,
          (∃ out : RestartCursor n, out.bitCursor ≤ head.length + t ∧
            returnScan r o₁ o₂ (finiteTape (head ++ bits.val)) s q w (k+1) current =
              some out ∧ out.state = target) →
          ∃ a, ∃ stop, stop ≤ head.length+t ∧
            f (finiteTape (head ++ bits.val)) = some (a,stop) ∧
            E (finiteTape (head ++ bits.val)) a stop := by
        intro bits
        rintro ⟨out, hc, hr, hs⟩
        simp only [returnScan, ha, if_true, hcursor] at hr
        obtain ⟨step, hf, htail⟩ := Option.bind_eq_some_iff.mp hr
        refine ⟨step.1, step.2, ?_, hf, out, hc, htail, hs⟩
        by_cases ht : (classifyState step.1).val = .transversal
        · simp only [ht, if_true] at htail
          cases Option.some.inj htail
          exact hc
        · simp only [ht, if_false] at htail
          exact (return_scan_success_interval r o₁ o₂ s q w k
            ⟨step.1,step.2,current.attempts+1⟩ _ out htail).1.trans hc
      have hsum : fairMass head t (fun tape => ∃ out : RestartCursor n,
          out.bitCursor ≤ head.length + t ∧
          returnScan r o₁ o₂ tape s q w (k+1) current = some out ∧ out.state = target) ≤
          ∑ a : PairedSet n, fairMass head t (fun tape => ∃ stop,
            stop ≤ head.length+t ∧ f tape = some (a,stop) ∧ E tape a stop) := by
        unfold fairMass
        rw [Finset.sum_comm]
        apply Finset.sum_le_sum
        intro bits _
        dsimp only
        split_ifs with h
        · obtain ⟨a, hs⟩ := hevent bits h
          apply le_trans (show (1 / (2 : ℝ)^t) ≤
            (if ∃ stop, stop ≤ head.length+t ∧
              f (finiteTape (head ++ bits.val)) = some (a,stop) ∧
              E (finiteTape (head ++ bits.val)) a stop then 1 / (2 : ℝ)^t else 0) by
                rw [if_pos hs])
          convert (Finset.single_le_sum (f := fun a =>
            if ∃ stop, stop ≤ head.length+t ∧
              f (finiteTape (head ++ bits.val)) = some (a,stop) ∧
              E (finiteTape (head ++ bits.val)) a stop then 1 / (2 : ℝ)^t else 0)
            (fun _ _ => by split_ifs <;> positivity) (Finset.mem_univ a)) using 1
          apply Finset.sum_congr rfl
          intro a _
          split_ifs <;> rfl
        · exact Finset.sum_nonneg (fun _ _ => by split_ifs <;> positivity)
      apply hsum.trans
      change _ ≤ ∑ a : PairedSet n, P current.state a * (hitWithin P A k).entry a target
      apply Finset.sum_le_sum
      intro a _
      have hbound := stopped_next_bound head t f
        (ChainStepIntervalReplay.chainStep_success_interval r o₁ o₂ s.drawTrials q w
          current.state head.length) a (fun tape stop => E tape a stop)
        ((hitWithin P A k).entry a target) ((hitWithin P A k).nonneg a target) (by
          intro stop hstart hstop pref hf
          have hpref : (head ++ pref.val).length = stop := by
            simp only [List.length_append, pref.2]
            omega
          have hbudget : (head ++ pref.val).length + (t-(stop-head.length)) = head.length+t := by
            rw [hpref]
            omega
          by_cases ht : (classifyState a).val = .transversal
          · have hA : a ∈ A := by simp [A, ht]
            rw [hitWithin_on_target P A k a target hA]
            by_cases heq : a = target
            · rw [if_pos heq]
              unfold fairMass
              calc
                _ ≤ ∑ _ : List.Vector Bool (t-(stop-head.length)),
                    1 / (2 : ℝ)^(t-(stop-head.length)) := by
                  apply Finset.sum_le_sum
                  intro bits _
                  split_ifs
                  · exact le_rfl
                  · positivity
                _ = 1 := by simp [card_vector]
            · rw [if_neg heq]
              have hnone : ∀ tape, ¬ E tape a stop := by
                intro tape
                rintro ⟨out, _, hr, hs⟩
                simp only [ht, if_true] at hr
                cases Option.some.inj hr
                exact heq hs
              simp only [fairMass, hnone, if_false, Finset.sum_const_zero, le_refl]
          · have hv := ChainStepNoninvalid.chainStep_noninvalid r o₁ o₂ _ s.drawTrials
              q w current.state head.length (a,stop) hvalid hf
            have hA : a ∉ A := by simp [A, ht]
            have hi := ih (head ++ pref.val) (t-(stop-head.length))
              ⟨a,stop,current.attempts+1⟩ hpref.symm hv
            rw [return_within_eq_hit_off_target P A k a target hA] at hi
            have heq : fairMass (head ++ pref.val) (t-(stop-head.length))
                (fun tape => E tape a stop) =
                fairMass (head ++ pref.val) (t-(stop-head.length)) (fun tape =>
                  ∃ out : RestartCursor n,
                    out.bitCursor ≤ (head ++ pref.val).length + (t-(stop-head.length)) ∧
                    returnScan r o₁ o₂ tape s q w k ⟨a,stop,current.attempts+1⟩ = some out ∧
                    out.state = target) := by
              unfold fairMass
              apply Finset.sum_congr rfl
              intro bits _
              simp only [E, ht, if_false, hbudget]
            rw [heq]
            exact hi)
      exact hbound.trans (mul_le_mul_of_nonneg_right (hstep head t current.state a hvalid)
        ((hitWithin P A k).nonneg a target))
    · have hz : fairMass head t (fun tape => ∃ out : RestartCursor n,
          out.bitCursor ≤ head.length+t ∧
          returnScan r o₁ o₂ tape s q w (k+1) current = some out ∧ out.state = target) = 0 := by
        simp only [returnScan, ha, if_false, reduceCtorEq, and_false, false_and,
          exists_false, fairMass, if_false, Finset.sum_const_zero]
      rw [hz]
      exact (returnWithin P A (k+1)).nonneg current.state target
