-- Prove2me | solution 1 for BitDFT.CallReturn.run_segment
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T02:22:52.417881+00:00
-- url     : https://prove2.me/submissions/c2308f05-a914-42d3-b673-1664a6384cbb

import Definitions.Def_BitDFT_CallReturn
import Mathlib.Logic.Function.Iterate

set_option autoImplicit false
namespace BitDFT.CallReturn
open IntMul

variable {M : MultitapeTM} (P Q : BitDFT.MachineSequence.Controller M)
  (call resume : P.K) (hcall : call ≠ P.exit)

private theorem step_fromP (c : P.machine.Cfg)
    (hExit : c.state ≠ P.exit) (hCall : c.state ≠ call) :
    (machine P Q call resume hcall).step (fromP P Q call resume hcall c) =
      fromP P Q call resume hcall (P.machine.step c) := by
  cases c with
  | mk state cells head =>
      change state ≠ P.exit at hExit
      change state ≠ call at hCall
      simp [machine, controller, fromP, MultitapeTM.step, hExit, hCall]

private theorem step_dispatch (c : P.machine.Cfg) (hc : c.state = call) :
    (machine P Q call resume hcall).step (fromP P Q call resume hcall c) =
      fromQ P Q call resume hcall (enterQ P Q call resume c) := by
  cases c with
  | mk state cells head =>
      change state = call at hc
      subst state
      simp [machine, controller, fromP, fromQ, enterQ, MultitapeTM.step, hcall]

private theorem step_fromQ (c : Q.machine.Cfg) (hExit : c.state ≠ Q.exit) :
    (machine P Q call resume hcall).step (fromQ P Q call resume hcall c) =
      fromQ P Q call resume hcall (Q.machine.step c) := by
  cases c with
  | mk state cells head =>
      change state ≠ Q.exit at hExit
      simp [machine, controller, fromQ, MultitapeTM.step, hExit]

private theorem step_return (c : Q.machine.Cfg) (hc : c.state = Q.exit) :
    (machine P Q call resume hcall).step (fromQ P Q call resume hcall c) =
      fromP P Q call resume hcall (returnP P Q call resume c) := by
  cases c with
  | mk state cells head =>
      change state = Q.exit at hc
      subst state
      simp [machine, controller, fromP, fromQ, returnP, MultitapeTM.step]

private theorem runP (c : P.machine.Cfg) (t : ℕ)
    (hAvoid : ∀ s < t, (P.machine.step^[s] c).state ≠ P.exit ∧
      (P.machine.step^[s] c).state ≠ call) :
    (machine P Q call resume hcall).step^[t]
      (fromP P Q call resume hcall c) =
    fromP P Q call resume hcall (P.machine.step^[t] c) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [Function.iterate_succ_apply', ih (by
        intro s hs
        exact hAvoid s (by omega))]
      rcases hAvoid t (by omega) with ⟨he, hc⟩
      rw [step_fromP P Q call resume hcall _ he hc]
      rw [Function.iterate_succ_apply']

private theorem runQ (c : Q.machine.Cfg) (t : ℕ)
    (hAvoid : ∀ s < t, (Q.machine.step^[s] c).state ≠ Q.exit) :
    (machine P Q call resume hcall).step^[t]
      (fromQ P Q call resume hcall c) =
    fromQ P Q call resume hcall (Q.machine.step^[t] c) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [Function.iterate_succ_apply', ih (by
        intro s hs
        exact hAvoid s (by omega))]
      rw [step_fromQ P Q call resume hcall _ (hAvoid t (by omega))]
      rw [Function.iterate_succ_apply']

/-- Exact clock for one call/return segment in a reusable controller. -/
theorem run_segment_local {M : MultitapeTM}
    (P Q : BitDFT.MachineSequence.Controller M)
    (call resume : P.K) (hcall : call ≠ P.exit)
    (c : P.machine.Cfg) (a b : ℕ)
    (hPavoid : ∀ s < a, (P.machine.step^[s] c).state ≠ P.exit ∧
      (P.machine.step^[s] c).state ≠ call)
    (hCall : (P.machine.step^[a] c).state = call)
    (hQavoid : ∀ s < b,
      (Q.machine.step^[s] (enterQ P Q call resume (P.machine.step^[a] c))).state ≠ Q.exit)
    (hQexit : (Q.machine.step^[b]
      (enterQ P Q call resume (P.machine.step^[a] c))).state = Q.exit) :
    (machine P Q call resume hcall).step^[a + 1 + b + 1]
      (fromP P Q call resume hcall c) =
    fromP P Q call resume hcall
      (returnP P Q call resume
        (Q.machine.step^[b] (enterQ P Q call resume (P.machine.step^[a] c)))) := by
  let cCall := P.machine.step^[a] c
  let qStart := enterQ P Q call resume cCall
  let qEnd := Q.machine.step^[b] qStart
  have hP := runP P Q call resume hcall c a hPavoid
  have hQ := runQ P Q call resume hcall qStart b hQavoid
  have hFirst :
      (machine P Q call resume hcall).step^[a + 1]
        (fromP P Q call resume hcall c) =
      fromQ P Q call resume hcall qStart := by
    rw [Function.iterate_succ_apply', hP]
    exact step_dispatch P Q call resume hcall cCall hCall
  have hLast :
      (machine P Q call resume hcall).step^[b + 1]
        (fromQ P Q call resume hcall qStart) =
      fromP P Q call resume hcall (returnP P Q call resume qEnd) := by
    rw [Function.iterate_succ_apply', hQ]
    exact step_return P Q call resume hcall qEnd hQexit
  calc
    (machine P Q call resume hcall).step^[a + 1 + b + 1]
        (fromP P Q call resume hcall c) =
      (machine P Q call resume hcall).step^[b + 1]
        ((machine P Q call resume hcall).step^[a + 1]
          (fromP P Q call resume hcall c)) := by
            rw [show a + 1 + b + 1 = (b + 1) + (a + 1) by omega,
              Function.iterate_add_apply]
    _ = (machine P Q call resume hcall).step^[b + 1]
        (fromQ P Q call resume hcall qStart) := by rw [hFirst]
    _ = fromP P Q call resume hcall (returnP P Q call resume qEnd) := hLast

end BitDFT.CallReturn

theorem solution {M : IntMul.MultitapeTM}
    (P Q : BitDFT.MachineSequence.Controller M)
    (call resume : P.K) (hcall : call ≠ P.exit)
    (c : P.machine.Cfg) (a b : ℕ)
    (hPavoid : ∀ s < a, (P.machine.step^[s] c).state ≠ P.exit ∧
      (P.machine.step^[s] c).state ≠ call)
    (hCall : (P.machine.step^[a] c).state = call)
    (hQavoid : ∀ s < b,
      (Q.machine.step^[s] (BitDFT.CallReturn.enterQ P Q call resume
        (P.machine.step^[a] c))).state ≠ Q.exit)
    (hQexit : (Q.machine.step^[b]
      (BitDFT.CallReturn.enterQ P Q call resume (P.machine.step^[a] c))).state = Q.exit) :
    (BitDFT.CallReturn.machine P Q call resume hcall).step^[a + 1 + b + 1]
      (BitDFT.CallReturn.fromP P Q call resume hcall c) =
    BitDFT.CallReturn.fromP P Q call resume hcall
      (BitDFT.CallReturn.returnP P Q call resume
        (Q.machine.step^[b] (BitDFT.CallReturn.enterQ P Q call resume
          (P.machine.step^[a] c)))) := by
  exact BitDFT.CallReturn.run_segment_local P Q call resume hcall c a b
    hPavoid hCall hQavoid hQexit
