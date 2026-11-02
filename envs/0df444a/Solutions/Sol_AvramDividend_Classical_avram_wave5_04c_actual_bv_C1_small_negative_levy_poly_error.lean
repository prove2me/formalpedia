-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04c_actual_bv_C1_small_negative_levy_poly_error
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T17:46:23.948984+00:00
-- url     : https://prove2.me/submissions/1a20996b-f410-4a30-bc54-00ea2321728c

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_small_negative_first_moment_integrable
import Theorems.Thm_AvramDividend_Classical_boundedVariation_full_negative_jump_increment_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_zero_poly_primitive_levy_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_C1_moving_base_residual_polynomial_first_moment_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Filter Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

/-! The true BV Lévy jump measure sees an arbitrarily small first-moment
error from one C1 exponential polynomial on its infinite-activity band. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (w : ℝ → ℝ) (hwC1 : ContDiff ℝ 1 w)
    (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ u v : ℝ, |w u - w v| ≤ L * |u - v|)
    (x : ℝ) (hgen : X.GeneratorIntegrable w x)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ p : Polynomial ℝ, Polynomial.eval 0 p = 0 ∧
      |∫ y in Ioo (-1 : ℝ) 0,
        (w (x + y) - w x) +
          (∫ r in (0 : ℝ)..(-y),
            Polynomial.eval (Real.exp (-r)) p) ∂X.ν| ≤
      ε * (∫ y in Ioo (-1 : ℝ) 0, -y ∂X.ν) := by
  obtain ⟨δ, hδ, p, hp0, hpBound⟩ :=
    avram_wave5_04c_C1_moving_base_residual_polynomial_first_moment_bound
      w hwC1 L hL hLip x 1 ε (by norm_num) hε
  refine ⟨p, hp0, ?_⟩
  let s : Set ℝ := Ioo (-1 : ℝ) 0
  let E : ℝ → ℝ := fun y =>
    (w (x + y) - w x) +
      (∫ r in (0 : ℝ)..(-y), Polynomial.eval (Real.exp (-r)) p)
  have hs : s ⊆ Iio (0 : ℝ) := by
    intro y hy
    exact hy.2
  have hW : IntegrableOn (fun y : ℝ => w (x + y) - w x) s X.ν :=
    (boundedVariation_full_negative_jump_increment_integrable X hBV w x hgen).mono_set hs
  have hP : IntegrableOn (fun y : ℝ =>
      ∫ r in (0 : ℝ)..(-y),
        Polynomial.eval (Real.exp (-r)) p) s X.ν :=
    (avram_wave5_04c_actual_bv_zero_poly_primitive_levy_integrable
      X hBV p hp0).mono_set hs
  have hE : IntegrableOn E s X.ν := hW.add hP
  have hR : IntegrableOn (fun y : ℝ => -y) s X.ν := by
    simpa only [s] using bv_small_negative_first_moment_integrable X hBV
  have hPt (y : ℝ) (hy : y ∈ s) :
      |E y| ≤ ε * (-y) := by
    have hR0 : 0 ≤ -y := by have h := hy.2; linarith
    have htail : ¬ (1 : ℝ) < -y := by
      have h := hy.1
      linarith
    have hp := hpBound x (-y) (by simpa using hδ) hR0
    simp only [if_neg htail, mul_zero, add_zero] at hp
    have hshift : x - -y = x + y := by ring
    rw [hshift] at hp
    calc
      |E y| = |-((w x - w (x + y)) -
          (∫ r in (0 : ℝ)..(-y),
            Polynomial.eval (Real.exp (-r)) p))| := by
              simp only [E]
              congr 1
              ring
      _ = |(w x - w (x + y)) -
          (∫ r in (0 : ℝ)..(-y),
            Polynomial.eval (Real.exp (-r)) p)| := abs_neg _
      _ ≤ ε * (-y) := hp
  have hAE : (fun y : ℝ => |E y|) ≤ᵐ[X.ν.restrict s]
      (fun y : ℝ => ε * (-y)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
    exact hPt y hy
  have hmono : (∫ y in s, |E y| ∂X.ν) ≤
      ∫ y in s, ε * (-y) ∂X.ν :=
    integral_mono_ae hE.abs (hR.const_mul ε) hAE
  calc
    |∫ y in Ioo (-1 : ℝ) 0,
      (w (x + y) - w x) +
        (∫ r in (0 : ℝ)..(-y),
          Polynomial.eval (Real.exp (-r)) p) ∂X.ν| =
      |∫ y in s, E y ∂X.ν| := rfl
    _ ≤ ∫ y in s, |E y| ∂X.ν := abs_integral_le_integral_abs
    _ ≤ ∫ y in s, ε * (-y) ∂X.ν := hmono
    _ = ε * (∫ y in Ioo (-1 : ℝ) 0, -y ∂X.ν) := by
      simp only [s, integral_const_mul]
