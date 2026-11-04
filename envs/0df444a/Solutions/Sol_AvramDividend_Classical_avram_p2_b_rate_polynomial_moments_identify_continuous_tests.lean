-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_b_rate_polynomial_moments_identify_continuous_tests
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T18:23:47.514581+00:00
-- url     : https://prove2.me/submissions/b4f5d2c5-975f-4855-9a10-47bc85ee8fd1

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_two_finite_measures_ae_comparison

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

theorem solution
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc (0 : ℝ) 1)
    (hν : ∀ᵐ x ∂ν, x ∈ Set.Icc (0 : ℝ) 1)
    (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc 0 1))
    (hfμ : Integrable f μ) (hfν : Integrable f ν)
    (hpoly : ∀ p : Polynomial ℝ,
      Integrable (fun x : ℝ => p.eval x) μ ∧
      Integrable (fun x : ℝ => p.eval x) ν ∧
      (∫ x, p.eval x ∂μ) = (∫ x, p.eval x ∂ν)) :
    (∫ x, f x ∂μ) = (∫ x, f x ∂ν) := by
  let S : ℝ := μ.real Set.univ + ν.real Set.univ
  have hS : 0 ≤ S := by
    dsimp [S]
    positivity
  have hDiff : ∀ ε : ℝ, 0 < ε →
      |(∫ x, f x ∂μ) - (∫ x, f x ∂ν)| ≤ ε := by
    intro ε hε
    let δ : ℝ := ε / (S + 1)
    have hden : 0 < S + 1 := by linarith
    have hδ : 0 < δ := div_pos hε hden
    obtain ⟨p, hp⟩ :=
      exists_polynomial_near_of_continuousOn (0 : ℝ) 1 f hf δ hδ
    obtain ⟨hpμ, hpν, heq⟩ := hpoly p
    have haeμ : ∀ᵐ x ∂μ, |f x - p.eval x| ≤ δ := by
      filter_upwards [hμ] with x hx
      rw [abs_sub_comm]
      exact le_of_lt (hp x hx)
    have haeν : ∀ᵐ x ∂ν, |f x - p.eval x| ≤ δ := by
      filter_upwards [hν] with x hx
      rw [abs_sub_comm]
      exact le_of_lt (hp x hx)
    have hbound :=
      AvramDividend.Classical.avram_p2_b_rate_two_finite_measures_ae_comparison
        μ ν f (fun x => p.eval x) hfμ hpμ hfν hpν δ haeμ haeν
    rw [heq, sub_self, abs_zero, zero_add] at hbound
    calc
      |(∫ x, f x ∂μ) - (∫ x, f x ∂ν)| ≤ δ * S := hbound
      _ ≤ δ * (S + 1) := mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hδ)
      _ = ε := by
        dsimp [δ]
        field_simp
  by_contra hne
  have hpos : 0 < |(∫ x, f x ∂μ) - (∫ x, f x ∂ν)| := by
    exact abs_pos.mpr (sub_ne_zero.mpr hne)
  have hsmall := hDiff (|(∫ x, f x ∂μ) - (∫ x, f x ∂ν)| / 2) (by linarith)
  linarith