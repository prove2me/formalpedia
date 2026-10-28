-- Prove2me | solution 1 for BitDFT.CallReturn.call_segment_run
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T22:51:19.575824+00:00
-- url     : https://prove2.me/submissions/76949faf-5a08-41ed-9669-404596dd165f

import Definitions.Def_BitDFT_CallReturn

set_option autoImplicit false
namespace BitDFT.CallReturn
open IntMul BitDFT.MachineSequence

theorem step_call {M : MultitapeTM} (P Q : Controller M) (call resume : P.K)
    (hcall : call ≠ P.exit) (c : P.machine.Cfg) (hc : c.state = call) :
    (machine P Q call resume hcall).step (fromP P Q call resume hcall c) =
      fromQ P Q call resume hcall (enterQ P Q call resume c) := by
  cases c
  cases hc
  simp [MultitapeTM.step, machine, controller, fromP, fromQ, enterQ, hcall]

theorem step_return {M : MultitapeTM} (P Q : Controller M) (call resume : P.K)
    (hcall : call ≠ P.exit) (d : Q.machine.Cfg) (hd : d.state = Q.exit) :
    (machine P Q call resume hcall).step (fromQ P Q call resume hcall d) =
      fromP P Q call resume hcall (returnP P Q call resume d) := by
  cases d
  cases hd
  simp [MultitapeTM.step, machine, controller, fromP, fromQ, returnP]

theorem runQ_before_return {M : MultitapeTM} (P Q : Controller M)
    (call resume : P.K) (hcall : call ≠ P.exit) (c : Q.machine.Cfg) (t : ℕ)
    (hbefore : ∀ s < t, (Q.machine.step^[s] c).state ≠ Q.exit) :
    (machine P Q call resume hcall).step^[t] (fromQ P Q call resume hcall c) =
      fromQ P Q call resume hcall (Q.machine.step^[t] c) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [Function.iterate_succ_apply', ih (by
        intro s hs
        exact hbefore s (by omega))]
      have hstate : (Q.machine.step^[t] c).state ≠ Q.exit := hbefore t (by omega)
      simp [MultitapeTM.step, machine, controller, fromQ, hstate,
        Function.iterate_succ_apply']

  theorem call_return_run_local {M : MultitapeTM} (P Q : Controller M)
      (call resume : P.K) (hcall : call ≠ P.exit)
      (c : P.machine.Cfg) (hc : c.state = call)
      (u : ℕ) (d : Q.machine.Cfg)
      (hbefore : ∀ s < u, (Q.machine.step^[s] (enterQ P Q call resume c)).state ≠ Q.exit)
      (hrun : Q.machine.step^[u] (enterQ P Q call resume c) = d)
      (hhalt : d.state = Q.exit) :
      (machine P Q call resume hcall).step^[u+2] (fromP P Q call resume hcall c) =
        fromP P Q call resume hcall (returnP P Q call resume d) := by
    have hbody : (machine P Q call resume hcall).step^[u]
        (fromQ P Q call resume hcall (enterQ P Q call resume c)) =
        fromQ P Q call resume hcall d := by
      rw [runQ_before_return P Q call resume hcall _ u hbefore, hrun]
    have hafter : (machine P Q call resume hcall).step^[u+1]
        (fromP P Q call resume hcall c) = fromQ P Q call resume hcall d := by
      rw [show u+1 = u+1 by rfl, Function.iterate_add_apply,
        Function.iterate_one, step_call P Q call resume hcall c hc, hbody]
    rw [show u+2 = (u+1)+1 by omega, Function.iterate_succ_apply', hafter,
      step_return P Q call resume hcall d hhalt]


theorem stepP_before_call {M : MultitapeTM} (P Q : Controller M)
    (call resume : P.K) (hcall : call ≠ P.exit) (c : P.machine.Cfg)
    (hstate : c.state ≠ call) :
    (machine P Q call resume hcall).step (fromP P Q call resume hcall c) =
      fromP P Q call resume hcall (P.machine.step c) := by
  cases c with
  | mk state cells head =>
      by_cases he : state = P.exit
      · subst state
        have hf := P.frozen (fun i => cells i (head i))
        simp [MultitapeTM.step, machine, controller, fromP, hf]
      · have hc : state ≠ call := hstate
        simp [MultitapeTM.step, machine, controller, fromP, he, hc]

theorem runP_before_call {M : MultitapeTM} (P Q : Controller M)
    (call resume : P.K) (hcall : call ≠ P.exit) (c : P.machine.Cfg) (t : ℕ)
    (hbefore : ∀ s < t, (P.machine.step^[s] c).state ≠ call) :
    (machine P Q call resume hcall).step^[t] (fromP P Q call resume hcall c) =
      fromP P Q call resume hcall (P.machine.step^[t] c) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [Function.iterate_succ_apply', ih (by
        intro s hs
        exact hbefore s (by omega))]
      have hs : (P.machine.step^[t] c).state ≠ call := hbefore t (by omega)
      rw [stepP_before_call P Q call resume hcall _ hs, Function.iterate_succ_apply']

/-- One scanner segment followed by one complete child call, with both
    dispatch transitions included in the exact total clock. -/
theorem call_segment_run_local {M : MultitapeTM} (P Q : Controller M)
    (call resume : P.K) (hcall : call ≠ P.exit)
    (c : P.machine.Cfg) (s : ℕ) (cCall : P.machine.Cfg)
    (hp : P.machine.step^[s] c = cCall)
    (hbeforeP : ∀ r < s, (P.machine.step^[r] c).state ≠ call)
    (hcCall : cCall.state = call)
    (u : ℕ) (d : Q.machine.Cfg)
    (hbeforeQ : ∀ r < u, (Q.machine.step^[r] (enterQ P Q call resume cCall)).state ≠ Q.exit)
    (hq : Q.machine.step^[u] (enterQ P Q call resume cCall) = d)
    (hhalt : d.state = Q.exit) :
    (machine P Q call resume hcall).step^[s+u+2] (fromP P Q call resume hcall c) =
      fromP P Q call resume hcall (returnP P Q call resume d) := by
  have hp' := runP_before_call P Q call resume hcall c s hbeforeP
  have hcallRun := call_return_run_local P Q call resume hcall cCall hcCall u d hbeforeQ hq hhalt
  calc
    (machine P Q call resume hcall).step^[s+u+2] (fromP P Q call resume hcall c)
        = (machine P Q call resume hcall).step^[u+2]
            ((machine P Q call resume hcall).step^[s] (fromP P Q call resume hcall c)) := by
              rw [show s+u+2 = (u+2)+s by omega, Function.iterate_add_apply]
    _ = (machine P Q call resume hcall).step^[u+2] (fromP P Q call resume hcall cCall) := by
          rw [hp', hp]
    _ = fromP P Q call resume hcall (returnP P Q call resume d) := hcallRun

end BitDFT.CallReturn

open IntMul BitDFT.MachineSequence BitDFT.CallReturn

theorem solution {M : MultitapeTM} (P Q : Controller M)
    (call resume : P.K) (hcall : call ≠ P.exit)
    (c : P.machine.Cfg) (s : ℕ) (cCall : P.machine.Cfg)
    (hp : P.machine.step^[s] c = cCall)
    (hbeforeP : ∀ r < s, (P.machine.step^[r] c).state ≠ call)
    (hcCall : cCall.state = call)
    (u : ℕ) (d : Q.machine.Cfg)
    (hbeforeQ : ∀ r < u, (Q.machine.step^[r] (enterQ P Q call resume cCall)).state ≠ Q.exit)
    (hq : Q.machine.step^[u] (enterQ P Q call resume cCall) = d)
    (hhalt : d.state = Q.exit) :
    (machine P Q call resume hcall).step^[s+u+2] (fromP P Q call resume hcall c) =
      fromP P Q call resume hcall (returnP P Q call resume d) := by
  exact call_segment_run_local P Q call resume hcall c s cCall hp hbeforeP hcCall u d hbeforeQ hq hhalt
