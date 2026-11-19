-- Prove2me | solution 1 for DeletionCode.ConcreteProgress.lift_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:58:17.205816+00:00
-- url     : https://prove2.me/submissions/00cb7586-844e-47f4-bd44-b76edb73d73e

import Definitions.Def_DeletionCode_ConcreteModel
import Definitions.Def_DeletionCode_ConcreteTransitions
import Definitions.Def_DeletionCode_ConcreteProgress
import Theorems.Thm_DeletionCode_ConcreteFill_fillFromBase_correct
import Theorems.Thm_DeletionCode_ConcreteModel_Model_complete_known
import Theorems.Thm_DeletionCode_ConcreteModel_Model_sound_update
import Theorems.Thm_DeletionCode_ConcreteModel_Model_window_bound
import Theorems.Thm_DeletionCode_ConcreteTransitions_startNegative_transition
import Theorems.Thm_DeletionCode_ConcreteTransitions_startPositive_transition
import Theorems.Thm_DeletionCode_HeaderRecovery_negativeExtra_lt
import Theorems.Thm_DeletionCode_PartialWords_readBits_sound
import Theorems.Thm_DeletionCode_PartialWords_writeBits_correct
import Theorems.Thm_DeletionCode_PathMemory_readPath_complete
import Theorems.Thm_DeletionCode_Recovery_State_start_wellFormed
import Theorems.Thm_DeletionCode_Recovery_step_preserves
import Theorems.Thm_DeletionCode_SelectedWindows_Realizes_fill_update
import Theorems.Thm_DeletionCode_SelectedWindows_Realizes_ready_seedKnown

section
namespace DeletionCode.ConcreteProgress
open Windows HeaderRecovery PartialWords SelectedWindows PathMemory
open ConcreteModel ConcreteDecoder ConcreteStart ConcreteFill ConcreteTransitions Recovery
variable {B : Type*} [DecidableEq B] {x : Letters} {n k : ℕ}
private theorem execute_start (M : Model B x n k)
    (s : State B) (mem : Bank B) (hi : M.Invariant s mem)
    (source : B) (sourceSide : Bool) (sourceOffset : ℕ)
    (dest : B) (destSide : Bool) (destOffset : ℕ) (bits : PartialWords.Bits k)
    (hread : readPath k (M.header source) (mem source) sourceSide sourceOffset k = some bits)
    (hbound : destOffset + k ≤ pathLength k (M.header dest) destSide)
    (hmatch : Matches bits (pathLetters k (M.header dest) (M.long dest) destSide) destOffset) :
    ∃ w extra mem',
      execute x n k M.header mem
        (.start source sourceSide sourceOffset dest destSide destOffset extra) = some mem' ∧
      M.Invariant (s.start dest w) mem' := by
  cases destSide with
  | false =>
    obtain ⟨w, t, ht, hreal, hsound⟩ := startNegative_transition s mem M.header M.long
      k dest destOffset bits hi.realizes hi.sound (M.rho_lower dest) (M.rho_upper dest)
      hbound hmatch
    refine ⟨w, false, Function.update mem dest t, ?_, ?_⟩
    · simp only [execute, hread, Option.bind_some, Bool.false_eq_true, ite_false,
        ht, Option.map_some]
    · exact ⟨State.start_wellFormed M.schedule s hi.wellFormed dest w, hsound, hreal⟩
  | true =>
    have hseed : ∀ i : Fin k,
        positivePath k (M.header dest) (M.long dest) (destOffset + i.val) = bits i :=
      fun i => (hmatch i).symm
    obtain ⟨extra, w, t, ht, hreal, hsound⟩ := startPositive_transition s mem M.header M.long
      k dest destOffset bits hi.realizes hi.sound (M.rho_lower dest) (M.rho_upper dest)
      (M.header_bit dest) hbound hseed
    refine ⟨w, extra, Function.update mem dest t, ?_, ?_⟩
    · simp only [execute, hread, Option.bind_some, ite_true,
        ht, Option.map_some]
    · exact ⟨State.start_wellFormed M.schedule s hi.wellFormed dest w, hsound, hreal⟩
end DeletionCode.ConcreteProgress
end

set_option autoImplicit true
open DeletionCode DeletionCode.ConcreteProgress
open Windows HeaderRecovery PartialWords SelectedWindows PathMemory
open ConcreteModel ConcreteDecoder ConcreteStart ConcreteFill ConcreteTransitions Recovery
variable {B : Type*} [DecidableEq B] {x : Letters} {n k : ℕ}
namespace DeletionCode.ConcreteProgress
theorem _root_.solution (M : Model B x n k) (hx : KUnique x n k)
    (s : State B) (mem : Bank B) (hi : M.Invariant s mem)
    {q : State B} (step : Recovery.Step M.schedule s q) :
    ∃ q' mem' instruction,
      Recovery.Step M.schedule s q' ∧
      execute x n k M.header mem instruction = some mem' ∧ M.Invariant q' mem' := by
  cases step with
  | startAdjacent a b w ha hab hb =>
    obtain ⟨sideA, sideB, i, j, hibound, hjbound, hagree⟩ := M.adjacent_seed a b hab
    obtain ⟨bits, hread, hmatch⟩ := readPath_complete k (M.header a) (M.long a) (mem a)
      sideA i k (M.rho_lower a) (M.rho_upper a) (M.header_bit a) (hi.sound a)
      (M.complete_known s mem hi.realizes a ha) hibound
    have htarget : Matches bits (pathLetters k (M.header b) (M.long b) sideB) j := by
      intro u
      exact (hmatch u).trans (hagree u.val u.isLt)
    obtain ⟨v, extra, mem', hexecute, hinvariant⟩ := execute_start M s mem hi
      a sideA i b sideB j bits hread hjbound htarget
    exact ⟨s.start b v, mem', .start a sideA i b sideB j extra,
      Step.startAdjacent s a b v ha hab hb, hexecute, hinvariant⟩
  | startSupplier b a w v hr hn hsrc ha =>
    obtain ⟨r, seed, hrbound, hseedread⟩ := hi.realizes.ready_seedKnown s mem
      (fun b => negativeExtra k (M.header b)) k b w
      (negativeExtra_lt k (M.header b) (M.rho_lower b) (M.rho_upper b)) hr
    obtain ⟨side, j, hjbound, hagree⟩ := M.supplier_occurrence b w a hsrc
    have hwindow := M.window_bound b w
    have hsourceBound : windowStart (negativeExtra k (M.header b)) w + r + k ≤
        negativeLength k (M.header b) := by
      change r + k ≤ windowLength k at hrbound
      omega
    have htargetBound : j + r + k ≤ pathLength k (M.header a) side := by
      change r + k ≤ windowLength k at hrbound
      omega
    have hsourceMatch := readBits_sound (mem b) (negativePath k (M.header b) (M.long b))
      (negativeLength k (M.header b)) (windowStart (negativeExtra k (M.header b)) w + r)
      k (hi.sound b) hsourceBound seed hseedread
    have htarget : Matches seed (pathLetters k (M.header a) (M.long a) side) (j + r) := by
      intro u
      calc
        seed u = negativePath k (M.header b) (M.long b)
            (windowStart (negativeExtra k (M.header b)) w + r + u.val) := hsourceMatch u
        _ = pathLetters k (M.header a) (M.long a) side (j + r + u.val) := by
          have hu : r + u.val < windowLength k := by
            have := u.isLt
            change r + k ≤ windowLength k at hrbound
            omega
          simpa only [Nat.add_assoc] using hagree (r + u.val) hu
    have hread : readPath k (M.header b) (mem b) false
        (windowStart (negativeExtra k (M.header b)) w + r) k = some seed := by
      simpa only [readPath, if_pos hsourceBound] using hseedread
    obtain ⟨newSlot, extra, mem', hexecute, hinvariant⟩ := execute_start M s mem hi
      b false (windowStart (negativeExtra k (M.header b)) w + r)
      a side (j + r) seed hread htargetBound htarget
    exact ⟨s.start a newSlot, mem',
      .start b false (windowStart (negativeExtra k (M.header b)) w + r)
        a side (j + r) extra,
      Step.startSupplier s b a w newSlot hr hn hsrc ha, hexecute, hinvariant⟩
  | fillBase b w hr hn hsrc =>
    obtain ⟨r, seed, hrbound, hseedread⟩ := hi.realizes.ready_seedKnown s mem
      (fun b => negativeExtra k (M.header b)) k b w
      (negativeExtra_lt k (M.header b) (M.rho_lower b) (M.rho_upper b)) hr
    obtain ⟨t, ht, hsound, hext, hknown⟩ := fillFromBase_correct x
      (negativePath k (M.header b) (M.long b)) n k (windowLength k) (mem b)
      (negativeLength k (M.header b)) (windowStart (negativeExtra k (M.header b)) w)
      r seed hx (hi.sound b) (M.window_bound b w) hrbound hseedread
      (M.base_occurrence b w hsrc)
    have hstep := Step.fillBase s b w hr hn hsrc
    refine ⟨s.fill b w, Function.update mem b t, .fillBase b w r, hstep, ?_, ?_⟩
    · simp only [execute, ht, Option.map_some]
    · exact ⟨step_preserves M.schedule hstep hi.wellFormed,
        M.sound_update mem hi.sound b t hsound,
        SelectedWindows.Realizes.fill_update s mem (fun b => negativeExtra k (M.header b))
          k hi.realizes b w t hext ⟨_, hknown⟩⟩
  | fillSupplier b a w hr hn hsrc ha =>
    obtain ⟨side, j, hjbound, hagree⟩ := M.supplier_occurrence b w a hsrc
    obtain ⟨bits, hread, hmatch⟩ := readPath_complete k (M.header a) (M.long a) (mem a)
      side j (windowLength k) (M.rho_lower a) (M.rho_upper a) (M.header_bit a) (hi.sound a)
      (M.complete_known s mem hi.realizes a ha) hjbound
    have htarget : Matches bits (negativePath k (M.header b) (M.long b))
        (windowStart (negativeExtra k (M.header b)) w) := by
      intro u
      exact (hmatch u).trans (hagree u.val u.isLt).symm
    obtain ⟨t, ht, hsound, hext, hknown⟩ := writeBits_correct (mem b)
      (negativePath k (M.header b) (M.long b)) (negativeLength k (M.header b))
      (windowStart (negativeExtra k (M.header b)) w) (windowLength k)
      (hi.sound b) (M.window_bound b w) bits htarget
    have hstep := Step.fillSupplier s b a w hr hn hsrc ha
    refine ⟨s.fill b w, Function.update mem b t, .fillSupplier a side j b w, hstep, ?_, ?_⟩
    · simp only [execute, hread, Option.bind_some, ht, Option.map_some]
    · exact ⟨step_preserves M.schedule hstep hi.wellFormed,
        M.sound_update mem hi.sound b t hsound,
        SelectedWindows.Realizes.fill_update s mem (fun b => negativeExtra k (M.header b))
          k hi.realizes b w t hext ⟨bits, hknown⟩⟩
end DeletionCode.ConcreteProgress
