-- Prove2me | solution 1 for BitDFT.CallReturn.repeated_call_segments
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T23:00:06.927286+00:00
-- url     : https://prove2.me/submissions/66e31fa5-9773-46ce-b2bd-de299f4323be

import Theorems.Thm_BitDFT_CallReturn_call_segment_run
import Theorems.Thm_BitDFT_MachineSequence_iterate_segments

set_option autoImplicit false
open IntMul BitDFT.MachineSequence BitDFT.CallReturn

theorem solution {M : MultitapeTM} (P Q : Controller M)
    (call resume : P.K) (hcall : call ≠ P.exit)
    (cfg : ℕ → P.machine.Cfg) (callCfg : ℕ → P.machine.Cfg)
    (result : ℕ → Q.machine.Cfg) (s u : ℕ → ℕ)
    (hscan : ∀ i, P.machine.step^[s i] (cfg i) = callCfg i)
    (hbeforeP : ∀ i r, r < s i → (P.machine.step^[r] (cfg i)).state ≠ call)
    (hcallState : ∀ i, (callCfg i).state = call)
    (hbeforeQ : ∀ i r, r < u i →
      (Q.machine.step^[r] (enterQ P Q call resume (callCfg i))).state ≠ Q.exit)
    (hchild : ∀ i, Q.machine.step^[u i] (enterQ P Q call resume (callCfg i)) = result i)
    (hhalt : ∀ i, (result i).state = Q.exit)
    (hnext : ∀ i, returnP P Q call resume (result i) = cfg (i + 1))
    (n : ℕ) :
    (machine P Q call resume hcall).step^[∑ i ∈ Finset.range n, (s i + u i + 2)]
      (fromP P Q call resume hcall (cfg 0)) =
      fromP P Q call resume hcall (cfg n) := by
  have hsegment : ∀ i,
      (machine P Q call resume hcall).step^[s i + u i + 2]
        (fromP P Q call resume hcall (cfg i)) =
      fromP P Q call resume hcall (cfg (i + 1)) := by
    intro i
    rw [BitDFT.CallReturn.call_segment_run P Q call resume hcall (cfg i) (s i)
      (callCfg i) (hscan i) (hbeforeP i) (hcallState i) (u i) (result i)
      (hbeforeQ i) (hchild i) (hhalt i), hnext i]
  exact BitDFT.MachineSequence.iterate_segments
    (machine P Q call resume hcall).step
    (fun i => fromP P Q call resume hcall (cfg i))
    (fun i => s i + u i + 2) hsegment n
