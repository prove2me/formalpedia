-- Prove2me | solution 1 for FirstPassageLinearTransport.collatzTerminalBinIndex_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:06:32.426347+00:00
-- url     : https://prove2.me/submissions/5fcba887-d87d-4775-8953-930172e687dd

import Definitions.Def_FirstPassageLinearTransport_TimeoutCore
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
import Theorems.Thm_FirstPassageLinearTransport_wordIncrementSum_collatz_le_length

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {m : ℕ} {B : ℝ} {v : Fin m → Bool}
    (hnonneg : 0 ≤ B + wordIncrementSum collatzLogIncrement v) :
    collatzTerminalBinIndex B v < m + ⌈B⌉₊ + 2 := by
  have hsum := wordIncrementSum_collatz_le_length v
  have hceil : B ≤ (⌈B⌉₊ : ℝ) := Nat.le_ceil B
  unfold collatzTerminalBinIndex
  rw [Nat.floor_lt hnonneg]
  push_cast
  linarith
end FirstPassageLinearTransport
