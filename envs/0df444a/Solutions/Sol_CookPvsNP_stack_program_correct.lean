-- Prove2me | solution 1 for CookPvsNP.stack_program_correct
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T13:24:45.043981+00:00
-- url     : https://prove2.me/submissions/76732f30-1ba5-4ce1-ad42-8a2d8740a0f6

import Definitions.Def_CookPvsNP_StackProgram
import Theorems.Thm_CookPvsNP_stack_trace_laws

set_option autoImplicit false
open CookPvsNP
open StackProg

private theorem compile {K A : Type} {p : StackProg K A} {s t : K → List A} {n : ℕ}
    (h : p.Exec s t n) : ∃ l : p.Label, p.done l = true ∧
      StackTrace p.machine n ⟨p.entry, s⟩ ⟨l, t⟩ := by
  induction h with
  | act f s =>
    refine ⟨true, rfl, .cons rfl ?_⟩
    exact .refl _
  | @seq p q s t u n m hp hq ihp ihq =>
    obtain ⟨lp, hdp, htp⟩ := ihp
    obtain ⟨lq, hdq, htq⟩ := ihq
    have hleft := (stack_trace_laws p.machine).2.2 (p.seq q).machine
      (fun c => ⟨Sum.inl c.state, c.store⟩) (by
        intro c hc
        change p.done c.state = false at hc
        simp [StackMachine.step, machine, done, next, hc]) htp
    have hright := (stack_trace_laws q.machine).2.2 (p.seq q).machine
      (fun c => ⟨Sum.inr c.state, c.store⟩) (by
        intro c hc
        change q.done c.state = false at hc
        simp [StackMachine.step, machine, done, next, hc]) htq
    have htransfer : StackTrace (p.seq q).machine 1 ⟨Sum.inl lp, t⟩ ⟨Sum.inr q.entry, t⟩ := by
      apply StackTrace.cons rfl
      simpa [StackMachine.step, machine, done, next, hdp, StackAct.apply] using
        (StackTrace.refl (P := (p.seq q).machine) (⟨Sum.inr q.entry, t⟩))
    refine ⟨Sum.inr lq, hdq, ?_⟩
    exact (stack_trace_laws (p.seq q).machine).2.1
      ((stack_trace_laws (p.seq q).machine).2.1 hleft htransfer) hright
  | @branchTrue test p q s t n ht hp ih =>
    obtain ⟨l, hd, hrun⟩ := ih
    have hbody := (stack_trace_laws p.machine).2.2 (StackProg.branch test p q).machine
      (fun c => ⟨some (Sum.inl c.state), c.store⟩) (by
        intro c hc
        change p.done c.state = false at hc
        simp [StackMachine.step, machine, done, next, hc]) hrun
    refine ⟨some (.inl l), hd, ?_⟩
    rw [Nat.add_comm]
    apply StackTrace.cons rfl
    simpa [StackMachine.step, machine, done, next, ht, StackAct.apply, entry] using hbody
  | @branchFalse test p q s t n ht hq ih =>
    obtain ⟨l, hd, hrun⟩ := ih
    have hbody := (stack_trace_laws q.machine).2.2 (StackProg.branch test p q).machine
      (fun c => ⟨some (Sum.inr c.state), c.store⟩) (by
        intro c hc
        change q.done c.state = false at hc
        simp [StackMachine.step, machine, done, next, hc]) hrun
    refine ⟨some (.inr l), hd, ?_⟩
    rw [Nat.add_comm]
    apply StackTrace.cons rfl
    simpa [StackMachine.step, machine, done, next, ht, StackAct.apply, entry] using hbody
  | @loopFalse test p s ht =>
    refine ⟨some none, rfl, .cons rfl ?_⟩
    simpa [StackMachine.step, machine, done, next, ht, StackAct.apply, entry] using
      (StackTrace.refl (P := (StackProg.loop test p).machine) ⟨some none, s⟩)
  | @loopTrue test p s t u n m ht hp hloop ihp ihloop =>
    obtain ⟨l, hd, hrun⟩ := ihp
    obtain ⟨l', hd', hrest⟩ := ihloop
    have hbody := (stack_trace_laws p.machine).2.2 (StackProg.loop test p).machine
      (fun c => ⟨some (some c.state), c.store⟩) (by
        intro c hc
        change p.done c.state = false at hc
        simp [StackMachine.step, machine, done, next, hc]) hrun
    have henter : StackTrace (StackProg.loop test p).machine (1 + n)
        ⟨none, s⟩ ⟨some (some l), t⟩ := by
      rw [Nat.add_comm]
      apply StackTrace.cons rfl
      simpa [StackMachine.step, machine, done, next, ht, StackAct.apply, entry] using hbody
    have htransfer : StackTrace (StackProg.loop test p).machine 1 ⟨some (some l), t⟩ ⟨none, t⟩ := by
      apply StackTrace.cons rfl
      simpa [StackMachine.step, machine, done, next, hd, StackAct.apply] using
        (StackTrace.refl (P := (StackProg.loop test p).machine) ⟨none, t⟩)
    exact ⟨l', hd', (stack_trace_laws (StackProg.loop test p).machine).2.1
      ((stack_trace_laws (StackProg.loop test p).machine).2.1 henter htransfer) hrest⟩

theorem solution {K A : Type} {p : StackProg K A} {s t : K → List A} {n : ℕ}
    (h : p.Exec s t n) : ∃ l : p.Label, p.done l = true ∧
      (p.machine.step^[n]) ⟨p.entry, s⟩ = ⟨l, t⟩ := by
  obtain ⟨l, hd, ht⟩ := compile h
  exact ⟨l, hd, (stack_trace_laws p.machine).1 ht⟩

#print axioms solution
