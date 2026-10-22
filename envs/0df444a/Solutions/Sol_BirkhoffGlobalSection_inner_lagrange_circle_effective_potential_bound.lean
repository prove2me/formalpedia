-- Prove2me | solution 1 for BirkhoffGlobalSection.inner_lagrange_circle_effective_potential_bound
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-24T07:49:42.379279+00:00
-- url     : https://prove2.me/submissions/1e22eb1b-e680-482d-86d3-50effc74114a

import Mathlib.Tactic
import Theorems.Thm_BirkhoffGlobalSection_jacobi_critical_momentum
import Theorems.Thm_BirkhoffGlobalSection_circle_reciprocal_distance_bound

open BirkhoffGlobalSection

theorem solution (μ : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1) (L : Phase)
    (hL : IsInnerLagrangePoint μ L) (s : Phase)
    (hr : ((leviCivitaPosition μ s) 0 + μ) ^ 2 +
      ((leviCivitaPosition μ s) 1) ^ 2 = (L 0 + μ) ^ 2) :
    zNormSq s * jacobiHamiltonian μ L ≤
      -(zNormSq s) *
        (((leviCivitaPosition μ s) 0) ^ 2 +
          ((leviCivitaPosition μ s) 1) ^ 2) / 2 -
      (1 - μ) / 2 -
      μ * zNormSq s / Real.sqrt (secondCollisionDistanceSq s) := by
  let r : ℝ := L 0 + μ
  let Z : ℝ := zNormSq s
  let a : ℝ := (leviCivitaPosition μ s) 0 + μ
  let b : ℝ := (leviCivitaPosition μ s) 1
  have hrpos : 0 < r := by dsimp [r]; linarith [hL.2.2.1]
  have hrone : r < 1 := by dsimp [r]; linarith [hL.2.2.2.1]
  have hZnonneg : 0 ≤ Z := by dsimp [Z, zNormSq]; positivity
  have hcomplex : a ^ 2 + b ^ 2 = (2 * Z) ^ 2 := by
    dsimp [a, b, Z, leviCivitaPosition, zNormSq]
    ring
  have hcircle : a ^ 2 + b ^ 2 = r ^ 2 := by
    simpa only [a, b, r] using hr
  have hZ : 2 * Z = r := by nlinarith [hcomplex, hcircle]
  have ha_lo : -r ≤ a := by nlinarith [sq_nonneg b, hcircle]
  have ha_hi : a ≤ r := by nlinarith [sq_nonneg b, hcircle]
  have hdist : secondCollisionDistanceSq s = 1 + r ^ 2 - 2 * a := by
    have hform : secondCollisionDistanceSq s = (a - 1) ^ 2 + b ^ 2 := by
      dsimp [secondCollisionDistanceSq, a, b, leviCivitaPosition]
      ring
    rw [hform]
    nlinarith [hcircle]
  have hscalar : r - a ≤ 1 / (1 - r) -
      1 / Real.sqrt (secondCollisionDistanceSq s) := by
    rw [hdist]
    exact circle_reciprocal_distance_bound r a hrpos hrone ha_lo ha_hi
  have hLy : L 1 = 0 := hL.2.2.2.2
  have hLroot1 : Real.sqrt ((L 0 + μ) ^ 2 + (L 1) ^ 2) = r := by
    calc
      _ = Real.sqrt ((L 0 + μ) ^ 2) := by rw [hLy]; ring
      _ = |L 0 + μ| := Real.sqrt_sq_eq_abs _
      _ = r := abs_of_pos hrpos
  have hLroot2 : Real.sqrt ((L 0 - 1 + μ) ^ 2 + (L 1) ^ 2) = 1 - r := by
    calc
      _ = Real.sqrt ((L 0 - 1 + μ) ^ 2) := by rw [hLy]; ring
      _ = |L 0 - 1 + μ| := Real.sqrt_sq_eq_abs _
      _ = 1 - r := by
        have hn : L 0 - 1 + μ < 0 := by dsimp [r] at hrone; linarith
        rw [abs_of_neg hn]
        dsimp [r]
        ring
  have hpL := jacobi_critical_momentum μ L hL.2.1
  have hH : jacobiHamiltonian μ L =
      -((r - μ) ^ 2 / 2 + (1 - μ) / r + μ / (1 - r)) := by
    unfold jacobiHamiltonian
    rw [hLroot1, hLroot2, hpL.1, hpL.2, hLy]
    dsimp [r]
    ring
  have hq : ((leviCivitaPosition μ s) 0) ^ 2 +
      ((leviCivitaPosition μ s) 1) ^ 2 =
      r ^ 2 + μ ^ 2 - 2 * μ * a := by
    have hqa : (leviCivitaPosition μ s) 0 = a - μ := by dsimp [a]; ring
    rw [hqa]
    change (a - μ) ^ 2 + b ^ 2 = r ^ 2 + μ ^ 2 - 2 * μ * a
    nlinarith [hcircle]
  have hmu : μ * (r - a) ≤ μ * (1 / (1 - r) -
      1 / Real.sqrt (secondCollisionDistanceSq s)) :=
    mul_le_mul_of_nonneg_left hscalar (le_of_lt hμ0)
  have hcore : (r - μ) ^ 2 / 2 + μ / (1 - r) ≥
      (r ^ 2 + μ ^ 2 - 2 * μ * a) / 2 +
        μ / Real.sqrt (secondCollisionDistanceSq s) := by
    simp only [div_eq_mul_inv] at hmu ⊢
    nlinarith only [hmu]
  have hweighted := mul_le_mul_of_nonneg_left hcore hZnonneg
  rw [hH, hq]
  have hrne : r ≠ 0 := ne_of_gt hrpos
  have hgrav : Z * ((1 - μ) / r) = (1 - μ) / 2 := by
    have hZeq : Z = r / 2 := by linarith [hZ]
    rw [hZeq]
    field_simp
  change Z * -((r - μ) ^ 2 / 2 + (1 - μ) / r + μ / (1 - r)) ≤
    -Z * (r ^ 2 + μ ^ 2 - 2 * μ * a) / 2 -
      (1 - μ) / 2 - μ * Z / Real.sqrt (secondCollisionDistanceSq s)
  simp only [div_eq_mul_inv] at hweighted hgrav ⊢
  nlinarith only [hweighted, hgrav]
