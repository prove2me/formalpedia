-- Prove2me | solution 1 for EinsteinFieldEquationsD.trace_of_field_equations
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-11T07:05:48.394064+00:00
-- url     : https://prove2.me/submissions/16addf09-c06f-4e69-a81e-7287619fc1c6

import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_EinsteinFieldEquationsD_Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open EinsteinFieldEquationsD

theorem solution {D : ℕ} (g T : Tensor2 D) (U : Set (Coord D))
    (Λ κ : ℝ) (hg : IsMetricOn g U)
    (hEFE : EinsteinFieldEquationsOn g T Λ κ U) :
    ∀ x ∈ U, scalarCurvature g x - ((D : ℝ) / 2) * scalarCurvature g x +
      (D : ℝ) * Λ = κ * metricTrace g T x := by
  intro x hx
  have hu : IsUnit (g x).det :=
    isUnit_iff_ne_zero.mpr (hg.nondegenerate x hx)
  have hgg : metricTrace g g x = (D : ℝ) := by
    change (∑ a : Fin D, ∑ b : Fin D, (g x)⁻¹ a b * g x a b) = _
    calc
      _ = ∑ a : Fin D, ((g x)⁻¹ * g x) a a := by
        apply Finset.sum_congr rfl
        intro a _
        rw [Matrix.mul_apply]
        apply Finset.sum_congr rfl
        intro b _
        rw [hg.symm x hx a b]
      _ = ∑ a : Fin D, (1 : Matrix (Fin D) (Fin D) ℝ) a a := by
        rw [Matrix.nonsing_inv_mul (g x) hu]
      _ = (D : ℝ) := by simp
  have hscale (c : ℝ) (F : Fin D → Fin D → ℝ) :
      (∑ a : Fin D, ∑ b : Fin D,
        invMetric g x a b * (c * F a b)) =
      c * (∑ a : Fin D, ∑ b : Fin D,
        invMetric g x a b * F a b) := by
    calc
      _ = ∑ a : Fin D, ∑ b : Fin D,
            c * (invMetric g x a b * F a b) := by
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        ring
      _ = _ := by simp only [Finset.mul_sum]
  have hE :
      (∑ a : Fin D, ∑ b : Fin D,
        invMetric g x a b * einsteinTensor g x a b) =
        scalarCurvature g x -
          (1 / 2 : ℝ) * scalarCurvature g x * metricTrace g g x := by
    calc
      _ = (∑ a : Fin D, ∑ b : Fin D,
          invMetric g x a b * ricci g x a b) -
          (∑ a : Fin D, ∑ b : Fin D,
          invMetric g x a b *
            ((1 / 2 : ℝ) * scalarCurvature g x * g x a b)) := by
            simp only [einsteinTensor, mul_sub, Finset.sum_sub_distrib]
      _ = _ := by
        rw [hscale ((1 / 2 : ℝ) * scalarCurvature g x)
          (fun a b => g x a b)]
        rfl
  have hsplit :
      (∑ a : Fin D, ∑ b : Fin D,
        invMetric g x a b *
          (einsteinTensor g x a b + Λ * g x a b)) =
      (∑ a : Fin D, ∑ b : Fin D,
        invMetric g x a b * einsteinTensor g x a b) +
          Λ * metricTrace g g x := by
    calc
      _ = (∑ a : Fin D, ∑ b : Fin D,
        invMetric g x a b * einsteinTensor g x a b) +
        (∑ a : Fin D, ∑ b : Fin D,
        invMetric g x a b * (Λ * g x a b)) := by
          simp only [mul_add, Finset.sum_add_distrib]
      _ = _ := by
        rw [hscale Λ (fun a b => g x a b)]
        rfl
  have hf :
      (∑ a : Fin D, ∑ b : Fin D,
        invMetric g x a b *
          (einsteinTensor g x a b + Λ * g x a b)) =
      (∑ a : Fin D, ∑ b : Fin D,
        invMetric g x a b * (κ * T x a b)) := by
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [hEFE x hx a b]
  calc
    scalarCurvature g x - ((D : ℝ) / 2) * scalarCurvature g x +
      (D : ℝ) * Λ =
        (∑ a : Fin D, ∑ b : Fin D,
          invMetric g x a b * einsteinTensor g x a b) +
          Λ * metricTrace g g x := by
            rw [hE, hgg]
            ring
    _ = ∑ a : Fin D, ∑ b : Fin D,
      invMetric g x a b *
        (einsteinTensor g x a b + Λ * g x a b) := hsplit.symm
    _ = ∑ a : Fin D, ∑ b : Fin D,
      invMetric g x a b * (κ * T x a b) := hf
    _ = κ * metricTrace g T x := by
      rw [hscale κ (fun a b => T x a b)]
      rfl
