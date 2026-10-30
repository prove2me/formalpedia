-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_01_deterministic_killed_qscale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T09:39:32.89416+00:00
-- url     : https://prove2.me/submissions/68596832-55ba-4d42-9913-326703a00566

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_perpetual_survival_markov
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_perpetual_survival_scale_real

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal

/-- The actual P-law closed-history q-killed deterministic semigroup identity,
independently derived from the true perpetual Esscher history Markov law. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q φ : ℝ) (hq : 0 < q) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (t : ℝ≥0) :
    (∫ ω, ({ω | ∀ v : ℝ≥0, v ≤ t → 0 ≤ x + X.X v ω}).indicator
      (fun ω => Real.exp (-(q * (t : ℝ))) * W (x + X.X t ω)) ω ∂P) =
      W x := by
  let C : ℝ → ℝ := fun y =>
    ⨅ u : ℝ≥0, ∫ ζ,
      ({ζ | ∀ v : ℝ≥0, v ≤ u → 0 ≤ y + X.X v ζ}).indicator
        (fun ζ => Real.exp
          (φ * X.X u ζ - (u : ℝ) * laplaceExponent X.c X.σ X.ν φ)) ζ ∂P
  let B : Set Ω := {ω | ∀ v : ℝ≥0, v ≤ t → 0 ≤ x + X.X v ω}
  obtain ⟨m, hm, hC⟩ :=
    avram_root29_01_perpetual_survival_scale_real
      X q φ hq hφ hroot W hW
  have hCEq (y : ℝ) :
      C y = m * Real.exp (-(φ * y)) * W y := hC y
  have hMarkov :=
    avram_root29_01_perpetual_survival_markov X φ hφ.le x t
  change C x =
    (∫ ω, B.indicator (fun ω =>
      Real.exp (φ * X.X t ω -
        (t : ℝ) * laplaceExponent X.c X.σ X.ν φ) *
        C (x + X.X t ω)) ω ∂P) at hMarkov
  have hPay (ω : Ω) :
      Real.exp (φ * X.X t ω -
        (t : ℝ) * laplaceExponent X.c X.σ X.ν φ) *
          (m * Real.exp (-(φ * (x + X.X t ω))) * W (x + X.X t ω)) =
      (m * Real.exp (-(φ * x))) *
        (Real.exp (-(q * (t : ℝ))) * W (x + X.X t ω)) := by
    have hψ : laplaceExponent X.c X.σ X.ν φ = q := hroot
    rw [hψ]
    have he :
        Real.exp (φ * X.X t ω - (t : ℝ) * q) *
          Real.exp (-(φ * (x + X.X t ω))) =
        Real.exp (-(φ * x)) * Real.exp (-(q * (t : ℝ))) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    calc
      _ = m *
          (Real.exp (φ * X.X t ω - (t : ℝ) * q) *
            Real.exp (-(φ * (x + X.X t ω)))) * W (x + X.X t ω) := by ring
      _ = m * (Real.exp (-(φ * x)) * Real.exp (-(q * (t : ℝ)))) *
            W (x + X.X t ω) := by rw [he]
      _ = _ := by ring
  have hIntegral :
      C x = (m * Real.exp (-(φ * x))) *
        (∫ ω, B.indicator (fun ω =>
          Real.exp (-(q * (t : ℝ))) * W (x + X.X t ω)) ω ∂P) := by
    calc
      C x = ∫ ω, B.indicator (fun ω =>
          Real.exp (φ * X.X t ω -
            (t : ℝ) * laplaceExponent X.c X.σ X.ν φ) *
            C (x + X.X t ω)) ω ∂P := hMarkov
      _ = ∫ ω, B.indicator (fun ω =>
          (m * Real.exp (-(φ * x))) *
            (Real.exp (-(q * (t : ℝ))) * W (x + X.X t ω))) ω ∂P := by
        apply integral_congr_ae
        filter_upwards with ω
        by_cases hw : ω ∈ B
        · simp only [Set.indicator_of_mem hw, hCEq (x + X.X t ω)]
          exact hPay ω
        · simp only [Set.indicator_of_notMem hw]
      _ = (m * Real.exp (-(φ * x))) *
          (∫ ω, B.indicator (fun ω =>
            Real.exp (-(q * (t : ℝ))) * W (x + X.X t ω)) ω ∂P) := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with ω
        by_cases hw : ω ∈ B
        · simp only [Set.indicator_of_mem hw]
        · simp only [Set.indicator_of_notMem hw, mul_zero]
  rw [hCEq x] at hIntegral
  have hfac : m * Real.exp (-(φ * x)) ≠ 0 :=
    mul_ne_zero (ne_of_gt hm) (Real.exp_ne_zero _)
  exact (mul_left_cancel₀ hfac hIntegral).symm
