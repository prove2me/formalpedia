-- Prove2me | solution 1 for AvramDividend.Classical.esscher_convex_shift_tendsto_atTop
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T15:48:02.917071+00:00
-- url     : https://prove2.me/submissions/827208f6-f6bf-41a6-b5a5-b4822871b1a3

import Mathlib.Analysis.Convex.Slope
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter

/-- A positive convex root gives linear growth of the shifted Laplace exponent. -/
theorem solution
    (psi : ℝ → ℝ) (phi q : ℝ)
    (hconv : ConvexOn ℝ (Ici (0 : ℝ)) psi)
    (hpsi0 : psi 0 = 0) (hphi : 0 < phi)
    (hq : 0 < q) (hpsiphi : psi phi = q) :
    Tendsto (fun beta : ℝ => psi (phi + beta) - q) atTop atTop := by
  have hbound : ∀ beta : ℝ, 0 ≤ beta →
      q * beta ≤ phi * (psi (phi + beta) - q) := by
    intro beta hbeta
    by_cases hb : beta = 0
    · subst beta
      simp [hpsiphi]
    · have hbpos : 0 < beta := lt_of_le_of_ne hbeta (Ne.symm hb)
      have hz : phi + beta ∈ Ici (0 : ℝ) := by
        change 0 ≤ phi + beta
        linarith
      have hs := hconv.secant_mono_aux1
        (x := (0 : ℝ)) (y := phi) (z := phi + beta)
        (by simp) hz hphi (by linarith)
      rw [hpsi0, hpsiphi] at hs
      nlinarith
  have hlin : Tendsto (fun beta : ℝ => (q / phi) * beta) atTop atTop :=
    Filter.Tendsto.const_mul_atTop (div_pos hq hphi) tendsto_id
  apply tendsto_atTop_mono' atTop ?_ hlin
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with beta hbeta
  calc
    (q / phi) * beta = (q * beta) / phi := by ring
    _ ≤ psi (phi + beta) - q :=
      (div_le_iff₀ hphi).2 (by nlinarith [hbound beta hbeta])
