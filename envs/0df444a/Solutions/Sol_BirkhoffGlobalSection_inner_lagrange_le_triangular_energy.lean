-- Prove2me | solution 1 for BirkhoffGlobalSection.inner_lagrange_le_triangular_energy
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-23T23:14:07.56182+00:00
-- url     : https://prove2.me/submissions/93a7cbf2-4f96-4de5-af43-8caae92b2eb0

import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Theorems.Thm_BirkhoffGlobalSection_jacobi_critical_momentum

open BirkhoffGlobalSection

theorem solution (μ : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1) (L : Phase)
    (hL : IsInnerLagrangePoint μ L) :
    jacobiHamiltonian μ L ≤ -(3 - μ + μ ^ 2) / 2 := by
  rcases hL with ⟨_, hcrit, hxlo, hxhi, hy⟩
  let r : ℝ := L 0 + μ
  let d : ℝ := 1 - μ - L 0
  have hr : 0 < r := by dsimp [r]; linarith
  have hd : 0 < d := by dsimp [d]; linarith
  have hsqrt₁ : Real.sqrt ((L 0 + μ) ^ 2 + (L 1) ^ 2) = r := by
    simp [hy, r, Real.sqrt_sq_eq_abs, abs_of_pos hr]
  have hneg : L 0 - 1 + μ < 0 := by linarith
  have hsqrt₂ : Real.sqrt ((L 0 - 1 + μ) ^ 2 + (L 1) ^ 2) = d := by
    calc
      _ = |L 0 - 1 + μ| := by simp [hy, Real.sqrt_sq_eq_abs]
      _ = d := by rw [abs_of_neg hneg]; dsimp [d]; ring
  have hp := jacobi_critical_momentum μ L hcrit
  have hH : jacobiHamiltonian μ L =
      -(L 0) ^ 2 / 2 - (1 - μ) / r - μ / d := by
    unfold jacobiHamiltonian
    rw [hsqrt₁, hsqrt₂, hp.1, hp.2, hy]
    ring
  have hrec_r : 2 - r ≤ 1 / r := by
    apply (le_div_iff₀ hr).2
    nlinarith [sq_nonneg (r - 1)]
  have hrec_d : 1 + r ≤ 1 / d := by
    apply (le_div_iff₀ hd).2
    dsimp [r, d]
    nlinarith [sq_nonneg (L 0 + μ)]
  have hweight₁ : (1 - μ) * (2 - r) ≤ (1 - μ) / r := by
    calc
      _ ≤ (1 - μ) * (1 / r) :=
        mul_le_mul_of_nonneg_left hrec_r (by linarith)
      _ = (1 - μ) / r := by ring
  have hweight₂ : μ * (1 + r) ≤ μ / d := by
    calc
      _ ≤ μ * (1 / d) := mul_le_mul_of_nonneg_left hrec_d (le_of_lt hμ0)
      _ = μ / d := by ring
  have hpoly : (3 - μ + μ ^ 2) / 2 +
      ((r - (1 - μ)) ^ 2 + μ * (1 - μ)) / 2 =
      (L 0) ^ 2 / 2 + (1 - μ) * (2 - r) + μ * (1 + r) := by
    dsimp [r]
    ring
  have hnonneg : 0 ≤ ((r - (1 - μ)) ^ 2 + μ * (1 - μ)) / 2 := by
    have hm : 0 ≤ μ * (1 - μ) := mul_nonneg (le_of_lt hμ0) (by linarith)
    nlinarith [sq_nonneg (r - (1 - μ))]
  have hbound : (3 - μ + μ ^ 2) / 2 ≤
      (L 0) ^ 2 / 2 + (1 - μ) / r + μ / d := by
    linarith [hweight₁, hweight₂, hpoly, hnonneg]
  rw [hH]
  linarith
