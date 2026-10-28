-- Prove2me | solution 1 for CountingMatroid.Bridge.sampledStack_eq_reverse_ofFn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T19:49:04.42919+00:00
-- url     : https://prove2.me/submissions/fc0117a6-fb0b-485a-9f68-2185aac0bd76

import Definitions.Def_CountingMatroidBridgeBalancedSampler

set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution {K : ℕ} (bits : ℕ → Bool) :
    CountingMatroid.Bridge.sampledStack bits K =
      (List.ofFn (fun i : Fin K => bits (3 * i.val + 1))).reverse := by
  induction K with
  | zero => rfl
  | succ K ih =>
      rw [CountingMatroid.Bridge.sampledStack, List.ofFn_succ']
      simp only [List.concat_eq_append, Fin.val_castSucc, Fin.val_last]
      rw [List.reverse_concat']
      simpa [Nat.mul_add] using congrArg (fun xs => bits (3 * K + 1) :: xs) ih
