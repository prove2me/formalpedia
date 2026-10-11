-- Prove2me | solution 1 for EinsteinFieldEquationsD.vacuum_field_equations_iff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-11T07:09:43.722735+00:00
-- url     : https://prove2.me/submissions/764629bc-b54d-480f-aa31-47aa8007c437

import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Definitions.Def_EinsteinFieldEquationsD_Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open EinsteinFieldEquationsD

theorem solution {D : ℕ} (hD : D ≠ 2) (g T : Tensor2 D)
    (U : Set (Coord D)) (Λ κ : ℝ) (hg : IsMetricOn g U)
    (x : Coord D) (hx : x ∈ U)
    (hT : ∀ a b : Fin D, T x a b = 0) :
    (∀ a b : Fin D, einsteinTensor g x a b +
      Λ * g x a b = κ * T x a b) ↔
    (∀ a b : Fin D, ricci g x a b =
      Λ / ((D : ℝ) / 2 - 1) * g x a b) := by
  have hdet : IsUnit (g x).det :=
    isUnit_iff_ne_zero.mpr (hg.nondegenerate x hx)
  have hgg : metricTrace g g x = (D : ℝ) := by
    change (∑ a : Fin D, ∑ b : Fin D,
      (g x)⁻¹ a b * g x a b) = _
    calc
      _ = ∑ a : Fin D, ((g x)⁻¹ * g x) a a := by
        apply Finset.sum_congr rfl
        intro a _
        rw [Matrix.mul_apply]
        apply Finset.sum_congr rfl
        intro b _
        rw [hg.symm x hx a b]
      _ = ∑ a : Fin D,
        (1 : Matrix (Fin D) (Fin D) ℝ) a a := by
          rw [Matrix.nonsing_inv_mul (g x) hdet]
      _ = (D : ℝ) := by simp
  have hscale (z : ℝ) (F : Fin D → Fin D → ℝ) :
      (∑ a : Fin D, ∑ b : Fin D,
        invMetric g x a b * (z * F a b)) =
      z * (∑ a : Fin D, ∑ b : Fin D,
        invMetric g x a b * F a b) := by
    calc
      _ = ∑ a : Fin D, ∑ b : Fin D,
          z * (invMetric g x a b * F a b) := by
            apply Finset.sum_congr rfl
            intro a _
            apply Finset.sum_congr rfl
            intro b _
            ring
      _ = _ := by simp only [Finset.mul_sum]
  let d : ℝ := (D : ℝ) / 2 - 1
  let q : ℝ := Λ / d
  have hdz : d ≠ 0 := by
    intro hz
    have hcast : (D : ℝ) = 2 := by dsimp [d] at hz; linarith
    exact hD (by exact_mod_cast hcast)
  have hq : q * d = Λ := by
    dsimp [q]
    exact div_mul_cancel₀ Λ hdz
  have hcoef : (1 / 2 : ℝ) * (q * (D : ℝ)) - Λ = q := by
    dsimp [d] at hq
    nlinarith [hq]
  constructor
  · intro h a b
    have heq (i j : Fin D) :
        ricci g x i j =
          ((1 / 2 : ℝ) * scalarCurvature g x - Λ) * g x i j := by
      have hh := h i j
      change ricci g x i j - (1 / 2 : ℝ) *
        scalarCurvature g x * g x i j +
        Λ * g x i j = κ * T x i j at hh
      rw [hT i j, mul_zero] at hh
      nlinarith
    have hscalar : scalarCurvature g x =
        ((1 / 2 : ℝ) * scalarCurvature g x - Λ) * (D : ℝ) := by
      change (∑ i : Fin D, ∑ j : Fin D,
        invMetric g x i j * ricci g x i j) = _
      calc
        _ = ∑ i : Fin D, ∑ j : Fin D,
          invMetric g x i j *
            (((1 / 2 : ℝ) * scalarCurvature g x - Λ) * g x i j) := by
              apply Finset.sum_congr rfl
              intro i _
              apply Finset.sum_congr rfl
              intro j _
              rw [heq i j]
        _ = ((1 / 2 : ℝ) * scalarCurvature g x - Λ) *
          metricTrace g g x := by
            rw [hscale ((1 / 2 : ℝ) * scalarCurvature g x - Λ)
              (fun i j => g x i j)]
            rfl
        _ = _ := by rw [hgg]
    have hr : scalarCurvature g x = q * (D : ℝ) := by
      apply (mul_left_cancel₀ hdz)
      dsimp [d]
      nlinarith [hscalar, hq]
    have ha := heq a b
    change ricci g x a b = q * g x a b
    rw [hr] at ha
    calc
      _ = ((1 / 2 : ℝ) * (q * (D : ℝ)) - Λ) * g x a b := ha
      _ = q * g x a b := by rw [hcoef]
  · intro h a b
    have hscalar : scalarCurvature g x = q * (D : ℝ) := by
      change (∑ i : Fin D, ∑ j : Fin D,
        invMetric g x i j * ricci g x i j) = _
      calc
        _ = ∑ i : Fin D, ∑ j : Fin D,
          invMetric g x i j * (q * g x i j) := by
            apply Finset.sum_congr rfl
            intro i _
            apply Finset.sum_congr rfl
            intro j _
            change invMetric g x i j * ricci g x i j =
              invMetric g x i j * (q * g x i j)
            rw [h i j]
        _ = q * metricTrace g g x := by
          rw [hscale q (fun i j => g x i j)]
          rfl
        _ = _ := by rw [hgg]
    have he := h a b
    change ricci g x a b = q * g x a b at he
    change ricci g x a b - (1 / 2 : ℝ) *
      scalarCurvature g x * g x a b +
      Λ * g x a b = κ * T x a b
    rw [he, hscalar, hT a b, mul_zero]
    calc
      _ = (q - (1 / 2 : ℝ) * (q * (D : ℝ)) + Λ) * g x a b := by ring
      _ = 0 := by rw [show q - (1 / 2 : ℝ) * (q * (D : ℝ)) + Λ = 0 by linarith [hcoef]]; ring
