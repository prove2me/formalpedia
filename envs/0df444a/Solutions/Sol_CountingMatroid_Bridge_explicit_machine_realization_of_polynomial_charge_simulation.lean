-- Prove2me | solution 1 for CountingMatroid.Bridge.explicit_machine_realization_of_polynomial_charge_simulation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T01:27:52.93988+00:00
-- url     : https://prove2.me/submissions/600ec6bd-8679-4fe9-94ee-71f78b02720e

import Definitions.Def_CountingMatroid_Bridge_ChargeSimulation
import Theorems.Thm_CountingMatroid_Bridge_execution_after_output
import Theorems.Thm_CountingMatroid_Bridge_finite_experiment_fpras_explicit
import Theorems.Thm_Cslib_polynomiallyBounded_iff_le
import Theorems.Thm_Cslib_PolynomiallyBounded_add
import Theorems.Thm_Cslib_PolynomiallyBounded_mul
import Theorems.Thm_Cslib_PolynomiallyBounded_pow
import Theorems.Thm_Cslib_PolynomiallyBounded_comp
set_option autoImplicit false
set_option maxHeartbeats 800000
open CountingMatroid.Model CountingMatroid.Model.Run CountingMatroid.Bridge

namespace Cslib.PolynomiallyBounded
variable {f : ℕ → ℕ}
theorem id : PolynomiallyBounded (fun n : ℕ => n) :=
  polynomiallyBounded_iff_le.mpr ⟨1, 1, by simp⟩
theorem const (c : ℕ) : PolynomiallyBounded (fun _ : ℕ => c) :=
  polynomiallyBounded_iff_le.mpr ⟨c, 0, by simp⟩
end Cslib.PolynomiallyBounded

theorem solution
    (simulation : PolynomialChargeSimulation) : ExplicitMachineRealization := by
  obtain ⟨k, s, P, overhead, hpoly, hsim⟩ := simulation
  obtain ⟨Cs, ds, _, hsource⟩ := finite_experiment_fpras_explicit
  have hinner : Cslib.PolynomiallyBounded (fun N => N + Cs * N ^ ds) :=
    Cslib.PolynomiallyBounded.id.add
      ((Cslib.PolynomiallyBounded.const Cs).mul (Cslib.PolynomiallyBounded.id.pow ds))
  obtain ⟨c, d, hbound⟩ := Cslib.polynomiallyBounded_iff_le.mp (hpoly.comp hinner)
  refine ⟨k, s, P, c * 2 ^ d + 1, d, by omega, ?_⟩
  intro n r M₁ M₂ O p hE₁ hE₂ hr₁ hr₂ hO
  let N := OAI.CommonBasesFPRAS.resourceBound 1 1 n r p.ε p.δ
  let H := N + Cs * N ^ ds
  let B := OAI.CommonBasesFPRAS.resourceBound (c * 2 ^ d + 1) d n r p.ε p.δ
  have hN : 0 < N := by
    simp only [N, OAI.CommonBasesFPRAS.resourceBound, one_mul, pow_one]
    omega
  have htime : overhead H ≤ B := by
    have hle := hbound N
    change overhead H ≤ c * (N + 1) ^ d at hle
    calc
      overhead H ≤ c * (N + 1) ^ d := hle
      _ ≤ c * (2 * N) ^ d := Nat.mul_le_mul_left c
        (Nat.pow_le_pow_left (by omega) d)
      _ = (c * 2 ^ d) * N ^ d := by rw [mul_pow]; ring
      _ ≤ (c * 2 ^ d + 1) * N ^ d := Nat.mul_le_mul_right _ (by omega)
      _ = B := by simp [B, N, OAI.CommonBasesFPRAS.resourceBound]
  obtain ⟨hK, _, hcost⟩ := hsource n r M₁ M₂ O p hE₁ hE₂ hr₁ hr₂ hO
  have hsourceBound : OAI.CommonBasesFPRAS.resourceBound Cs ds n r p.ε p.δ ≤ H := by
    simp only [H, N, OAI.CommonBasesFPRAS.resourceBound, one_mul, pow_one]
    omega
  obtain ⟨positions, hrun⟩ := hsim n r M₁ M₂ O p hE₁ hE₂ hr₁ hr₂ hO H
    (by dsimp [H]; omega) (hK.trans hsourceBound) (by
      intro xs hxs
      obtain ⟨_, _, hc, hb⟩ := hcost xs hxs
      exact ⟨hc.trans hsourceBound, hb.trans hsourceBound⟩)
  refine ⟨positions.trans (Fin.castLEEmb htime), ?_⟩
  intro bits
  obtain ⟨hout, hc, hb⟩ := hrun bits
  have hhalt : (OAI.CommonBasesFPRAS.execution P O
      (OAI.CommonBasesFPRAS.initialConfig k s n r p.ε p.δ) bits (overhead H)).output.isSome := by
    rw [hout]; rfl
  have hstable := execution_after_output P O
    (OAI.CommonBasesFPRAS.initialConfig k s n r p.ε p.δ) bits htime hhalt
  change (OAI.CommonBasesFPRAS.execution P O
    (OAI.CommonBasesFPRAS.initialConfig k s n r p.ε p.δ) bits B).output = _ ∧ _
  rw [hstable]
  exact ⟨hout, hc.trans htime, hb.trans htime⟩
