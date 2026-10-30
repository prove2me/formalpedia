-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_05_ioc_neumann_powers_mass_summable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T23:45:07.779974+00:00
-- url     : https://prove2.me/submissions/861d6b49-d1bc-45cd-ba66-a6220443d1c1

import Mathlib.Analysis.SpecificLimits.Basic
import Theorems.Thm_AvramDividend_Classical_causal_l1_convolution_power_exact_mass_geometric

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set

/-- Every native Ioc power recursion has globally summable geometric masses. -/
theorem solution
    (κ : ℝ → ℝ) (F : ℕ → ℝ → ℝ)
    (hκL1 : IntegrableOn κ (Ioi (0 : ℝ)) volume)
    (hFzero : F 0 = κ)
    (hFrec : ∀ n : ℕ, F (n + 1) =
      fun x : ℝ => ∫ s in Ioc (0 : ℝ) x,
        κ s * F n (x - s) ∂volume)
    (hρ0 : 0 ≤ ∫ x in Ioi (0 : ℝ), κ x ∂volume)
    (hρ1 : (∫ x in Ioi (0 : ℝ), κ x ∂volume) < 1) :
    (∀ n : ℕ, IntegrableOn (F n) (Ioi (0 : ℝ)) volume) ∧
    Summable (fun n : ℕ =>
      ∫ x in Ioi (0 : ℝ), F n x ∂volume) := by
  obtain ⟨G, hGzero, hGrec, hGL1, hGmass⟩ :=
    causal_l1_convolution_power_exact_mass_geometric κ hκL1
  have hEq : ∀ n : ℕ, F n = G n := by
    intro n
    induction n with
    | zero => exact hFzero.trans hGzero.symm
    | succ n ih =>
      rw [hFrec n, hGrec n, ih]
  constructor
  · intro n
    rw [hEq n]
    exact hGL1 n
  · have hM : (fun n : ℕ =>
        ∫ x in Ioi (0 : ℝ), F n x ∂volume) =
        fun n : ℕ =>
          (∫ x in Ioi (0 : ℝ), κ x ∂volume) ^ (n + 1) := by
      funext n
      rw [hEq n]
      exact hGmass n
    rw [hM]
    simpa only [pow_succ] using
      (Summable.mul_right (∫ x in Ioi (0 : ℝ), κ x ∂volume)
        (summable_geometric_of_lt_one hρ0 hρ1))
