-- Prove2me | solution 1 for BitDFT.encComplex_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T00:53:20.116569+00:00
-- url     : https://prove2.me/submissions/5f49d843-c983-45e9-ae7a-9a29d398c0a7

import Definitions.Def_BitDFT_Encoding
import Mathlib.Data.List.OfFn
import Mathlib.Tactic

set_option autoImplicit false
open BitDFT IntMul

/-- Each real or imaginary fixed-width signed field occupies a sign bit and
    exactly w magnitude bits. -/
theorem solution (w : ℕ) (z : ℤ × ℤ) :
    (encComplex w z).length = 2 * (w + 1) := by
  simp [encComplex, encInt, IntMul.bin, List.length_ofFn]
  omega
