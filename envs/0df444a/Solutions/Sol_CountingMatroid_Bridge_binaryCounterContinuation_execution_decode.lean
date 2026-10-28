-- Prove2me | solution 1 for CountingMatroid.Bridge.binaryCounterContinuation_execution_decode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T20:01:29.821676+00:00
-- url     : https://prove2.me/submissions/e6178f16-86d2-4701-b762-0f1b4d0f8105

import Definitions.Def_CountingMatroidBridgeBinarySampler

set_option autoImplicit false
set_option maxHeartbeats 800000
open OAI.CommonBasesFPRAS CountingMatroid.Bridge

theorem solution {s n K : ℕ}
    (P : Program 2 s) (O : IndependenceOracle n)
    (c : MachineConfig 2 (s + 15)) (bits : ℕ → Bool)
    (hcontrol : c.control = (⟨0, by omega⟩ : Fin (s + 15 + 1)))
    (houtput : c.output = none) (hscratch : c.registers 6 = [])
    (hcounter : c.registers 8 = []) (t : ℕ) :
    let input := binarySamplerInput c K
    let totalPrefix := binaryCounterCountdownSteps K K.bits + (3 * K + 1)
    let sampled := execution (binaryCounterThenProgram P) O input bits totalPrefix
    binaryCounterDecodeConfig
        (execution (binaryCounterThenProgram P) O input bits (totalPrefix + t)) =
      execution P O (binaryCounterProgramStartConfig sampled)
        (fun j => bits (totalPrefix + j)) t := by
  exact binaryCounterThenSampler_then_program P O c bits
    hcontrol houtput hscratch hcounter t
