-- Prove2me | solution 1 for BlockCycleRotation.rotate_block_step
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T10:36:10.189347+00:00
-- url     : https://prove2.me/submissions/28703069-6683-4303-9706-9b96cdb640ab

import Definitions.Def_BlockCycleRotation_Algorithm
import Definitions.Def_BlockCycleRotation_Euclid
import Mathlib

variable {α : Type*}

namespace BlockCycleRotation

@[simp]
theorem remSum_zero (n : ℕ) : remSum n 0 = 0 := by
  rw [remSum]; simp

@[simp]
theorem cost_zero (n : ℕ) : cost n 0 = 0 := by
  rw [cost]; simp

@[simp]
theorem finalSeg_zero (n : ℕ) : finalSeg n 0 = n := by
  rw [finalSeg]; simp

end BlockCycleRotation

open BlockCycleRotation in
/-- **The block cycle step.**

With `m = ⌊n / k⌋ * k` the length of the part covered by whole blocks, splitting
`l = P ++ Q` with `P = l.take m` and `Q = l.drop m`:

* `P.drop k` (the first `(b-1) * k` entries) is already in final position, and
* the remaining suffix is `(P.take k ++ Q).rotate k`, a rotation of a list of
  length `k + n % k` — the subproblem the algorithm recurses on. -/
theorem solution (l : List α) {k : ℕ} (hk : 0 < k) (hkn : k ≤ l.length) :
    l.rotate k =
      (l.take (l.length / k * k)).drop k ++
        ((l.take (l.length / k * k)).take k ++ l.drop (l.length / k * k)).rotate k:= by
  set n := l.length with hn
  set m := n / k * k with hm
  have hmn : m ≤ n := Nat.div_mul_le_self n k
  have hb : 1 ≤ n / k := (Nat.one_le_div_iff hk).2 hkn
  have hkm : k ≤ m := by
    calc k = 1 * k := (one_mul k).symm
      _ ≤ n / k * k := Nat.mul_le_mul_right k hb
  have hPlen : (l.take m).length = m := by
    rw [List.length_take]
    omega
  -- the first `k` entries of `l` are the first `k` entries of `P`
  have htakek : l.take k = (l.take m).take k := by
    rw [List.take_take]
    congr 1
    omega
  -- dropping `k` from `l` splits as dropping `k` from `P`, then all of `Q`
  have hdropk : l.drop k = (l.take m).drop k ++ l.drop m := by
    conv_lhs => rw [← List.take_append_drop m l]
    rw [List.drop_append_of_le_length (by omega)]
  -- the inner rotation just swaps the two pieces
  have hinner : ((l.take m).take k ++ l.drop m).rotate k
      = l.drop m ++ (l.take m).take k := by
    have hlen : ((l.take m).take k).length = k := by
      rw [List.length_take, hPlen]
      omega
    have hle : k ≤ ((l.take m).take k ++ l.drop m).length := by
      rw [List.length_append, hlen]
      omega
    rw [List.rotate_eq_drop_append_take hle, List.drop_left' hlen, List.take_left' hlen]
  rw [List.rotate_eq_drop_append_take hkn, hdropk, htakek, hinner, List.append_assoc]
