-- Prove2me | solution 1 for BitDFT.scalar_output_call
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T00:33:08.398115+00:00
-- url     : https://prove2.me/submissions/cc1f328b-a364-4da2-ab0c-97a5d5ea60f8

import Theorems.Thm_BitDFT_low_operand_call_input
import Theorems.Thm_BitDFT_scaled_call_word
import Definitions.Def_BitDFT_Encoding

set_option autoImplicit false
open BitDFT BitDFT.LowOperandCopy IntMul

theorem solution (M : MultitapeTM) (q n : ℕ) (z : ℤ) (T : ℝ)
    (hq : 1 ≤ q) (hnq : n < 2^q)
    (hqwide : lg n + 1 ≤ q) (hnwide : n ≤ 2^(lg n))
    (hz : z.natAbs ≤ 2^q) (hM : MultipliesAt M q T) :
    let h : sourceTape ≠ counterTape := (show sourceTape ≠ counterTape from by decide)
    let sign := decide (z < 0)
    let mag := z.natAbs
    let high := mag.testBit q
    let bits := bin q (mag % 2^q)
    encInt (q+1) z = sign :: high :: bits ∧
    (∃ tc : ℕ, tc ≤ q+5 ∧
      (machine h).step^[tc] (initial h sign high bits) = final h sign high bits) ∧
    (final h sign high bits).cells ⟨1, by simp [storage]⟩ =
      storage.tapeOf (bits.map storage.bitSym) ∧
    (∃ tm : ℕ, (tm : ℝ) ≤ 36*T ∧
      (IntMul.TrackedNativeCall.machine M).HaltsWithOutput
        (bin q n) (bin q (mag % 2^q)) tm (bin (2*q) (n*(mag % 2^q)))) ∧
    (if high then n*2^q else n*(mag % 2^q)) = n*mag ∧
    bin (2*q) (if high then n*2^q else n*(mag % 2^q)) =
      List.replicate (2*q-(q+lg n+1)) false ++
        bin (q+lg n+1) (if high then n*2^q else n*(mag % 2^q)) := by
  dsimp only
  obtain ⟨henc, ⟨tc, htc, hcopy⟩, hcopyTape⟩ :=
    BitDFT.low_operand_call_input q z
  obtain ⟨tm, htm, hcall, hselect, hpad⟩ :=
    BitDFT.scaled_call_word M q n z.natAbs T hq hnq hqwide hnwide hz hM
  refine ⟨henc, ⟨tc, ?_, hcopy⟩, hcopyTape, ⟨tm, htm, ?_⟩, ?_, ?_⟩
  · omega
  · simpa only using hcall
  · simpa only using hselect
  · simpa only using hpad
