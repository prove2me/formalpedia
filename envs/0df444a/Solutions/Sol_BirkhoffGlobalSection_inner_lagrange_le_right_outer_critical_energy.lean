-- Prove2me | solution 1 for BirkhoffGlobalSection.inner_lagrange_le_right_outer_critical_energy
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-23T23:32:45.316992+00:00
-- url     : https://prove2.me/submissions/805f0030-5033-4968-a601-02c153010cc9

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Theorems.Thm_BirkhoffGlobalSection_jacobi_critical_momentum
import Theorems.Thm_BirkhoffGlobalSection_jacobi_partial_position_one
import Theorems.Thm_BirkhoffGlobalSection_outer_inverse_distance_potential_min
import Theorems.Thm_BirkhoffGlobalSection_inner_outer_reflection_potential

open BirkhoffGlobalSection

theorem solution (μ : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1) (L : Phase)
    (hL : IsInnerLagrangePoint μ L) (s : Phase)
    (hfree : collisionFree μ s)
    (hcrit : isCriticalPoint (jacobiHamiltonian μ) s)
    (haxis : s 1 = 0) (hright : 1 - μ < s 0) :
    jacobiHamiltonian μ L ≤ jacobiHamiltonian μ s := by
  rcases hL with ⟨_, hLcrit, hLlow, hLhigh, hLaxis⟩
  let u : ℝ := s 0 - 1 + μ
  let v : ℝ := 1 - μ - L 0
  have hu : 0 < u := by dsimp [u]; linarith
  have hv : 0 < v := by dsimp [v]; linarith
  have hv1 : v < 1 := by dsimp [v]; linarith
  have hSpos₁ : 0 < s 0 + μ := by linarith
  have hSpos₂ : 0 < s 0 - 1 + μ := by linarith
  have hLpos₁ : 0 < L 0 + μ := by linarith
  have hLneg₂ : L 0 - 1 + μ < 0 := by linarith
  have hSroot₁ : Real.sqrt ((s 0 + μ) ^ 2 + (s 1) ^ 2) = 1 + u := by
    calc
      _ = |s 0 + μ| := by simp [haxis, Real.sqrt_sq_eq_abs]
      _ = 1 + u := by rw [abs_of_pos hSpos₁]; dsimp [u]; ring
  have hSroot₂ : Real.sqrt ((s 0 - 1 + μ) ^ 2 + (s 1) ^ 2) = u := by
    calc
      _ = |s 0 - 1 + μ| := by simp [haxis, Real.sqrt_sq_eq_abs]
      _ = u := by rw [abs_of_pos hSpos₂]
  have hLroot₁ : Real.sqrt ((L 0 + μ) ^ 2 + (L 1) ^ 2) = 1 - v := by
    calc
      _ = |L 0 + μ| := by simp [hLaxis, Real.sqrt_sq_eq_abs]
      _ = 1 - v := by rw [abs_of_pos hLpos₁]; dsimp [v]; ring
  have hLroot₂ : Real.sqrt ((L 0 - 1 + μ) ^ 2 + (L 1) ^ 2) = v := by
    calc
      _ = |L 0 - 1 + μ| := by simp [hLaxis, Real.sqrt_sq_eq_abs]
      _ = v := by rw [abs_of_neg hLneg₂]; dsimp [v]; ring
  have hpL := jacobi_critical_momentum μ L hLcrit
  have hps := jacobi_critical_momentum μ s hcrit
  have hHL : jacobiHamiltonian μ L =
      -((1 - μ - v) ^ 2 / 2 + μ / v + (1 - μ) / (1 - v)) := by
    unfold jacobiHamiltonian
    rw [hLroot₁, hLroot₂, hpL.1, hpL.2, hLaxis]
    dsimp [v]
    ring
  have hHS : jacobiHamiltonian μ s =
      -((1 - μ + u) ^ 2 / 2 + μ / u + (1 - μ) / (1 + u)) := by
    unfold jacobiHamiltonian
    rw [hSroot₁, hSroot₂, hps.1, hps.2, haxis]
    dsimp [u]
    ring
  have hzero : partialDerivative (jacobiHamiltonian μ) s 0 = 0 := by
    simp [partialDerivative, hcrit.2]
  have hder := jacobi_partial_position_one μ s hfree
  rw [hzero, hps.2, hSroot₁, hSroot₂] at hder
  have hq₁ : s 0 + μ = 1 + u := by dsimp [u]; ring
  have hq₂ : s 0 - 1 + μ = u := by rfl
  rw [hq₁, hq₂] at hder
  have hratio₁ : (1 - μ) * (1 + u) / (1 + u) ^ 3 =
      (1 - μ) / (1 + u) ^ 2 := by
    have hne : 1 + u ≠ 0 := ne_of_gt (by linarith : 0 < 1 + u)
    field_simp <;> ring
  have hratio₂ : μ * u / u ^ 3 = μ / u ^ 2 := by
    have hne : u ≠ 0 := ne_of_gt hu
    field_simp <;> ring
  rw [hratio₁, hratio₂] at hder
  have hs0 : s 0 = 1 - μ + u := by dsimp [u]; ring
  rw [hs0] at hder
  have hbal : u + (1 - μ) = μ / u ^ 2 + (1 - μ) / (1 + u) ^ 2 := by
    ring_nf at hder ⊢
    linarith
  have hmin := outer_inverse_distance_potential_min (1 - μ) μ (1 - μ) u v
    (le_of_lt hμ0) (by linarith) hu hv hbal
  have href := inner_outer_reflection_potential (1 - μ) v
    (by linarith) hv hv1
  have hcmp : (1 - μ + u) ^ 2 / 2 + μ / u + (1 - μ) / (1 + u) ≤
      (1 - μ - v) ^ 2 / 2 + μ / v + (1 - μ) / (1 - v) := by
    nlinarith [hmin, href]
  rw [hHL, hHS]
  linarith
