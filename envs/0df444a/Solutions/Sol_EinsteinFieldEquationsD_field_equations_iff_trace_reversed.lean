-- Prove2me | solution 1 for EinsteinFieldEquationsD.field_equations_iff_trace_reversed
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-11T07:23:16.853752+00:00
-- url     : https://prove2.me/submissions/acba952a-7b56-480a-8705-3997e9dbd1ee

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
    (x : Coord D) (hx : x ∈ U) :
    (∀ a b : Fin D, einsteinTensor g x a b + Λ * g x a b = κ * T x a b) ↔
      (∀ a b : Fin D, ricci g x a b -
        (2 / ((D : ℝ) - 2)) * Λ * g x a b =
        κ * (T x a b - (1 / ((D : ℝ) - 2)) *
          metricTrace g T x * g x a b)) := by
  let C : ℝ := (D : ℝ) - 2
  let τ : ℝ := metricTrace g T x
  let S : ℝ := scalarCurvature g x
  let q : ℝ := (2 * Λ - κ * τ) / C
  have hC : C ≠ 0 := by
    intro h
    have he : (D : ℝ) = 2 := by dsimp [C] at h; linarith
    exact hD (by exact_mod_cast he)
  have hq : q * C = 2 * Λ - κ * τ := by
    dsimp [q]
    exact div_mul_cancel₀ _ hC
  have hdet : IsUnit (g x).det :=
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
        rw [Matrix.nonsing_inv_mul (g x) hdet]
      _ = (D : ℝ) := by simp
  have hscale (z : ℝ) (F : Fin D → Fin D → ℝ) :
      (∑ a : Fin D, ∑ b : Fin D, invMetric g x a b * (z * F a b)) =
      z * (∑ a : Fin D, ∑ b : Fin D, invMetric g x a b * F a b) := by
    calc
      _ = ∑ a : Fin D, ∑ b : Fin D,
          z * (invMetric g x a b * F a b) := by
            apply Finset.sum_congr rfl
            intro a _
            apply Finset.sum_congr rfl
            intro b _
            ring
      _ = _ := by simp only [Finset.mul_sum]
  have htrace (z : ℝ)
      (h : ∀ a b : Fin D, ricci g x a b = κ * T x a b + z * g x a b) :
      S = κ * τ + z * (D : ℝ) := by
    change (∑ a : Fin D, ∑ b : Fin D,
      invMetric g x a b * ricci g x a b) = _
    calc
      _ = ∑ a : Fin D, ∑ b : Fin D, invMetric g x a b *
        (κ * T x a b + z * g x a b) := by
          apply Finset.sum_congr rfl
          intro a _
          apply Finset.sum_congr rfl
          intro b _
          rw [h a b]
      _ = (∑ a : Fin D, ∑ b : Fin D, invMetric g x a b *
        (κ * T x a b)) +
        (∑ a : Fin D, ∑ b : Fin D, invMetric g x a b *
          (z * g x a b)) := by
            simp only [mul_add, Finset.sum_add_distrib]
      _ = κ * metricTrace g T x + z * metricTrace g g x := by
        rw [hscale κ (fun a b => T x a b),
          hscale z (fun a b => g x a b)]
        rfl
      _ = κ * τ + z * (D : ℝ) := by rw [hgg]
  have hscalar_coeff (z : ℝ) (hs : S = κ * τ + z * (D : ℝ))
      (hz : z * C = 2 * Λ - κ * τ) :
      z = (1 / 2 : ℝ) * S - Λ := by
    dsimp [C] at hz
    nlinarith [hs, hz]
  have hbridge (a b : Fin D) :
      (ricci g x a b - (2 / C) * Λ * g x a b =
        κ * (T x a b - (1 / C) * τ * g x a b)) ↔
      (ricci g x a b = κ * T x a b + q * g x a b) := by
    constructor
    · intro h
      dsimp [q] at *
      field_simp [hC] at h ⊢
      nlinarith [h]
    · intro h
      dsimp [q] at *
      field_simp [hC] at h ⊢
      nlinarith [h]
  constructor
  · intro h
    let z : ℝ := (1 / 2 : ℝ) * S - Λ
    have hr (a b : Fin D) :
        ricci g x a b = κ * T x a b + z * g x a b := by
      have hh := h a b
      change ricci g x a b - (1 / 2 : ℝ) *
        scalarCurvature g x * g x a b + Λ * g x a b =
        κ * T x a b at hh
      dsimp [z, S]
      nlinarith [hh]
    have hs := htrace z hr
    have hzc : z * C = 2 * Λ - κ * τ := by
      dsimp [z, C]
      dsimp [z] at hs
      nlinarith [hs]
    have he : z = q := by
      apply (mul_right_cancel₀ hC)
      rw [hq]
      exact hzc
    intro a b
    change ricci g x a b - (2 / C) * Λ * g x a b =
      κ * (T x a b - (1 / C) * τ * g x a b)
    exact (hbridge a b).2 (by rw [← he]; exact hr a b)
  · intro h
    have hr (a b : Fin D) :
        ricci g x a b = κ * T x a b + q * g x a b :=
      (hbridge a b).1 (h a b)
    have hs := htrace q hr
    have he := hscalar_coeff q hs hq
    intro a b
    have hh := hr a b
    change ricci g x a b - (1 / 2 : ℝ) *
      scalarCurvature g x * g x a b + Λ * g x a b =
      κ * T x a b
    change q = (1 / 2 : ℝ) * scalarCurvature g x - Λ at he
    rw [hh, he]
    ring
