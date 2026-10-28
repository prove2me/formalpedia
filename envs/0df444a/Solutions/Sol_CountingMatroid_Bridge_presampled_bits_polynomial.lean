-- Prove2me | solution 1 for CountingMatroid.Bridge.presampled_bits_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T19:31:20.97756+00:00
-- url     : https://prove2.me/submissions/b9a387de-2206-41c8-bdbd-c4912f3506f6

import Mathlib
import Definitions.Def_CountingMatroid_Model_Run
import Definitions.Def_CommonBasesFPRAS
import Definitions.Def_CountingMatroid_Bridge_Presampling
import Theorems.Thm_CountingMatroid_Analysis_ScheduleValueEnvelope_schedule_value_envelope
import Theorems.Thm_CountingMatroid_Bridge_schedule_drawCalls_eq

set_option autoImplicit false
set_option maxHeartbeats 800000

open CountingMatroid CountingMatroid.Model CountingMatroid.Model.Run CountingMatroid.Model.Operations
open CountingMatroid.Bridge

namespace CountingMatroid.Bridge

private theorem flat_budget_bound (n I : ℕ) (s : AnnealingSchedule) (Q : ℕ)
    (hQ : 1 ≤ Q) (hn : n + 1 ≤ Q) (hI : I + 1 ≤ Q)
    (hL : s.L + 1 ≤ Q) (hA : s.restartCap ≤ Q)
    (hO : s.observations + 1 ≤ Q) (hD : s.drawTrials ≤ Q)
    (hR : s.repetitions ≤ Q)
    (hc : s.drawCalls = 3 * s.L * (s.restartCap + s.observations)) :
    s.repetitions * (n * s.L + s.drawCalls *
      (1 + s.drawTrials * (1000000 * (s.L + 1)^4 * (n + 1)^4 *
        (s.observations + 1)^4 * (I + 1)^4)) + 10) ≤
      6000017 * Q^20 := by
  have hn' : n ≤ Q := by omega
  have hL' : s.L ≤ Q := by omega
  have hO' : s.observations ≤ Q := by omega
  have hw : 1000000 * (s.L + 1)^4 * (n + 1)^4 *
      (s.observations + 1)^4 * (I + 1)^4 ≤ 1000000 * Q^16 := by
    calc
      _ ≤ 1000000 * Q^4 * Q^4 * Q^4 * Q^4 := by
        exact Nat.mul_le_mul
          (Nat.mul_le_mul
            (Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hL 4))
              (Nat.pow_le_pow_left hn 4)) (Nat.pow_le_pow_left hO 4))
          (Nat.pow_le_pow_left hI 4)
      _ = _ := by ring
  have hcalls : s.drawCalls ≤ 6 * Q^2 := by
    rw [hc]
    calc
      _ ≤ 3 * Q * (Q + Q) := Nat.mul_le_mul (Nat.mul_le_mul_left 3 hL')
        (Nat.add_le_add hA hO')
      _ = _ := by ring
  have hinner : 1 + s.drawTrials *
      (1000000 * (s.L + 1)^4 * (n + 1)^4 *
        (s.observations + 1)^4 * (I + 1)^4) ≤ 1000001 * Q^17 := by
    have hp : 1 ≤ Q^17 := one_le_pow₀ hQ
    have hm := Nat.mul_le_mul hD hw
    calc
      _ ≤ 1 + Q * (1000000 * Q^16) := Nat.add_le_add_left hm 1
      _ ≤ Q^17 + Q * (1000000 * Q^16) := Nat.add_le_add_right hp _
      _ = _ := by ring
  have hprod := Nat.mul_le_mul hcalls hinner
  have hnL : n * s.L ≤ Q^19 := by
    calc
      _ ≤ Q * Q := Nat.mul_le_mul hn' hL'
      _ = Q^2 := by ring
      _ ≤ Q^19 := Nat.pow_le_pow_right (by omega) (by omega)
  have hten : 10 ≤ 10 * Q^19 := by
    simpa using Nat.mul_le_mul_left 10 (one_le_pow₀ hQ : 1 ≤ Q^19)
  have hb : n * s.L + s.drawCalls *
      (1 + s.drawTrials * (1000000 * (s.L + 1)^4 * (n + 1)^4 *
        (s.observations + 1)^4 * (I + 1)^4)) + 10 ≤ 6000017 * Q^19 := by
    calc
      _ ≤ Q^19 + (6 * Q^2) * (1000001 * Q^17) + 10 * Q^19 :=
        Nat.add_le_add (Nat.add_le_add hnL hprod) hten
      _ = _ := by ring
  calc
    _ ≤ Q * (6000017 * Q^19) := Nat.mul_le_mul hR hb
    _ = _ := by ring

end CountingMatroid.Bridge

/-- Sampling every prescribed bit, including unused bits, costs polynomially
many coin draws in the source input-size parameter. This theorem concerns
the number of bits, not the implementation cost of the estimator. -/
theorem solution :
    ∃ C d : ℕ, ∀ (n r : ℕ) (p : InputParams),
      (Program.schedule n p).val.repetitions * blockLength n r p ≤
        C * (n + binaryInputLength n r p + Nat.ceil p.ε⁻¹ +
          binaryNatLength (Nat.ceil p.δ⁻¹) + 1)^d := by
  obtain ⟨C, d, h⟩ := Analysis.ScheduleValueEnvelope.schedule_value_envelope
  refine ⟨6000017 * (C + 2)^20, (d + 1)*20, ?_⟩
  intro n r p
  let X := n + binaryInputLength n r p + Nat.ceil p.ε⁻¹ +
    binaryNatLength (Nat.ceil p.δ⁻¹) + 1
  let s := (Program.schedule n p).val
  let Q := (C + 2) * X^(d + 1)
  have hX : 1 ≤ X := by dsimp [X]; omega
  have hXP : X ≤ X^(d + 1) := by
    simpa using Nat.pow_le_pow_right (by omega : 0 < X) (by omega : 1 ≤ d + 1)
  have hP : X^d ≤ X^(d + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hbound := h n r p
  change n + s.L + s.τ + s.restartCap + s.observations + s.drawTrials +
    binaryRatLength s.ρ + s.repetitions + 1 ≤ C * X^d at hbound
  have hbudget : C * X^d + X + 1 ≤ Q := by
    have hm := Nat.mul_le_mul_left C hP
    have hp : 1 ≤ X^(d + 1) := one_le_pow₀ hX
    dsimp [Q]
    nlinarith
  have hQ : 1 ≤ Q := by omega
  have hI : binaryInputLength n r p + 1 ≤ Q := by
    have : binaryInputLength n r p + 1 ≤ X := by dsimp [X]; omega
    omega
  have hb := flat_budget_bound n (binaryInputLength n r p) s Q hQ
    (by omega) hI (by omega) (by omega) (by omega) (by omega) (by omega)
    (schedule_drawCalls_eq n p)
  change s.repetitions * blockLength n r p ≤ _
  change s.repetitions * blockLength n r p ≤ 6000017 * Q^20 at hb
  calc
    _ ≤ 6000017 * Q^20 := hb
    _ = _ := by
      change 6000017 * ((C + 2) * X^(d + 1))^20 =
        (6000017 * (C + 2)^20) * X^((d + 1)*20)
      rw [mul_pow, ← pow_mul, mul_assoc]
