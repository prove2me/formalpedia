-- Prove2me | solution 1 for BitDFT.scaled_product_serialize_block
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T23:04:58.602188+00:00
-- url     : https://prove2.me/submissions/cd2582f0-22da-47c2-bc67-f306b5f6c43b

import Definitions.Def_BitDFT_CountedBlock
import Theorems.Thm_BitDFT_counted_block_correct
import Theorems.Thm_BitDFT_scalar_scaled_word_complete_v2
import Mathlib.Tactic

set_option autoImplicit false
open IntMul

/-- The accepted fixed-width product word is the exact source frame for a
    counted block copy of the shorter scaler output word. -/
theorem solution (q n a : ℕ) (hq : lg n + 1 ≤ q)
    (hn : n ≤ 2^(lg n)) (ha : a ≤ 2^q)
    (out descriptor : List Bool)
    (hdescWidth : val descriptor + 1 = q + lg n + 1) :
    let w := q + lg n + 1
    let z := if a.testBit q then n * 2^q else n * (a % 2^q)
    ∃ t : ℕ, t ≤ 6*w + 4*descriptor.length + 2 ∧
      IntMul.CountedStream.machine.step^[t]
        (BitDFT.CountedBlock.frame (List.replicate (2*q-w) false) out
          (bin w z) descriptor descriptor.reverse 0 .emit) =
        BitDFT.CountedBlock.frame (List.replicate (2*q-w) false) out
          (bin w z) descriptor descriptor.reverse (val descriptor+1) .halt ∧
      bin (2*q) (n*a) = List.replicate (2*q-w) false ++ bin w (n*a) := by
  dsimp only
  let w := q + lg n + 1
  let z := if a.testBit q then n * 2^q else n * (a % 2^q)
  have hscaled := BitDFT.scalar_scaled_word_complete_v2 q n a hq hn ha
  have hvalue : z = n*a := hscaled.1
  have hwidth : w ≤ 2*q := by omega
  have hrunlen : (bin w z).length = w := by simp [IntMul.bin, w]
  have hdescEnough : val descriptor + 1 ≤ (bin w z).length := by
    rw [hrunlen]
    simpa [w] using hdescWidth.le
  obtain ⟨t, ht, hrun⟩ := BitDFT.counted_block_correct
    (List.replicate (2*q-w) false) out (bin w z) descriptor hdescEnough
  refine ⟨t, ?_, hrun, ?_⟩
  · have htb := ht
    rw [hdescWidth] at htb
    simpa [w] using htb
  · simpa [w, z, hvalue] using hscaled.2.2
