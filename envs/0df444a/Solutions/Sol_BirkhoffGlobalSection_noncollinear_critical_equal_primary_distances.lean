-- Prove2me | solution 1 for BirkhoffGlobalSection.noncollinear_critical_equal_primary_distances
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-23T22:45:03.880133+00:00
-- url     : https://prove2.me/submissions/8e090707-b856-4063-8b10-b8c399451fc0

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Theorems.Thm_BirkhoffGlobalSection_jacobi_partial_position_one
import Theorems.Thm_BirkhoffGlobalSection_jacobi_critical_momentum
import Theorems.Thm_BirkhoffGlobalSection_noncollinear_critical_vertical_balance

open BirkhoffGlobalSection

theorem solution (μ : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1) (s : Phase)
    (hfree : collisionFree μ s)
    (hcrit : isCriticalPoint (jacobiHamiltonian μ) s)
    (hoffaxis : s 1 ≠ 0) :
    (s 0 + μ) ^ 2 + (s 1) ^ 2 =
      (s 0 - 1 + μ) ^ 2 + (s 1) ^ 2 := by
  let d₁ : ℝ := (s 0 + μ) ^ 2 + (s 1) ^ 2
  let d₂ : ℝ := (s 0 - 1 + μ) ^ 2 + (s 1) ^ 2
  let r₁ : ℝ := Real.sqrt d₁
  let r₂ : ℝ := Real.sqrt d₂
  let A : ℝ := (1 - μ) / r₁ ^ 3
  let B : ℝ := μ / r₂ ^ 3
  have hvert : A + B = 1 :=
    noncollinear_critical_vertical_balance μ hμ0 hμ1 s hfree hcrit hoffaxis
  have hp₃ : s 3 = -(s 0) := (jacobi_critical_momentum μ s hcrit).2
  have hz₀ : partialDerivative (jacobiHamiltonian μ) s 0 = 0 := by
    simp [partialDerivative, hcrit.2]
  have hforce : 0 = -(s 0) + (1 - μ) * (s 0 + μ) / r₁ ^ 3 +
      μ * (s 0 - 1 + μ) / r₂ ^ 3 := by
    simpa only [hz₀, hp₃] using jacobi_partial_position_one μ s hfree
  have hforce' : 0 = -(s 0) + A * (s 0 + μ) + B * (s 0 - 1 + μ) := by
    calc
      0 = -(s 0) + (1 - μ) * (s 0 + μ) / r₁ ^ 3 +
          μ * (s 0 - 1 + μ) / r₂ ^ 3 := hforce
      _ = _ := by dsimp [A, B]; ring
  have hmul : (s 0) * (A + B) = s 0 := by rw [hvert]; ring
  have hlin : μ * A - (1 - μ) * B = 0 := by
    nlinarith [hforce', hmul]
  have hweights : μ * (1 - μ) * (1 / r₁ ^ 3 - 1 / r₂ ^ 3) = 0 := by
    calc
      _ = μ * A - (1 - μ) * B := by dsimp [A, B]; ring
      _ = 0 := hlin
  have hweightpos : 0 < μ * (1 - μ) := mul_pos hμ0 (sub_pos.mpr hμ1)
  have hinv : 1 / r₁ ^ 3 = 1 / r₂ ^ 3 :=
    sub_eq_zero.mp ((mul_eq_zero.mp hweights).resolve_left (ne_of_gt hweightpos))
  have hpow : r₁ ^ 3 = r₂ ^ 3 := by
    have h := congrArg (fun x : ℝ => x⁻¹) hinv
    simpa only [one_div, inv_inv] using h
  have hr : r₁ = r₂ := by
    apply (pow_left_inj₀ (Real.sqrt_nonneg d₁) (Real.sqrt_nonneg d₂)
      (by norm_num : (3 : ℕ) ≠ 0)).mp
    exact hpow
  have hsquared := congrArg (fun x : ℝ => x ^ 2) hr
  change (Real.sqrt d₁) ^ 2 = (Real.sqrt d₂) ^ 2 at hsquared
  rw [Real.sq_sqrt (show 0 ≤ d₁ from le_of_lt hfree.1),
    Real.sq_sqrt (show 0 ≤ d₂ from le_of_lt hfree.2)] at hsquared
  exact hsquared
