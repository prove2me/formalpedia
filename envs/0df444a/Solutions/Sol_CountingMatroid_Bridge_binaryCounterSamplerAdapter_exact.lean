-- Prove2me | solution 1 for CountingMatroid.Bridge.binaryCounterSamplerAdapter_exact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T19:54:25.387495+00:00
-- url     : https://prove2.me/submissions/b7903c8c-8b9f-4c58-96e7-14df4c90d601

import Definitions.Def_CountingMatroidBridgeBinarySampler

set_option autoImplicit false
set_option maxHeartbeats 800000
open OAI.CommonBasesFPRAS CountingMatroid.Bridge

theorem solution
    {s n r K H : ℕ} (P : Program 2 s) (O : IndependenceOracle n)
    (tape : Fin (26 * (H + 1) ^ 2) → Bool) (hK : K ≤ H)
    (ε δ : ℚ) :
    let c := initialConfig 2 (s + 15) n r ε δ
    let bits := fun t => finiteBits tape t
    let counterSteps := binaryCounterCountdownSteps K K.bits
    let prefixLength := counterSteps + (3 * K + 1)
    let sampled := execution (binaryCounterThenProgram P) O
      (binarySamplerInput c K) bits prefixLength
    sampled.control.val = 15 ∧ sampled.output = none ∧
      sampled.registers 9 = List.ofFn (fun i : Fin K =>
        tape (binaryCounterSamplingPositionsPolynomialReversed K H hK i)) ∧
      sampled.oracleCalls = 0 ∧ sampled.bitOperations = prefixLength := by
  exact binaryCounterThenSampler_polynomialTape_handoff P O tape hK ε δ
