-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_cr_new_native_positive_root_derivative_coefficient
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T23:56:45.978864+00:00
-- url     : https://prove2.me/submissions/5c188c0d-1588-492e-b9e1-bf1a8e7dbf00

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_gaussian_native_esscher_real_kernel_denominator
import Theorems.Thm_AvramDividend_Classical_gaussian_native_double_tail_kernel_full_regularity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

/-- The true Esscher derivative is the native LK denominator's linear coefficient. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (q φ m : ℝ)
    (hφ : 0 < φ) (hroot : X.ψ φ = q) (hm : HasDerivAt X.ψ m φ) :
    m = X.c - (X.ν.map (fun y : ℝ => -y)).real ({1} : Set ℝ) + X.σ ^ 2 * φ +
      (∫ z in Ioi (0 : ℝ), (if z ≤ 1 then z else 0) - z * Real.exp (-φ * z)
        ∂(X.ν.map (fun y : ℝ => -y))) := by
  let A : ℝ := X.c - (X.ν.map (fun y : ℝ => -y)).real ({1} : Set ℝ) +
    X.σ ^ 2 * φ + (∫ z in Ioi (0 : ℝ), (if z ≤ 1 then z else 0) -
      z * Real.exp (-φ * z) ∂(X.ν.map (fun y : ℝ => -y)))
  let K : ℝ → ℝ := fun t =>
    (∫⁻ z : ℝ, if 0 < t ∧ t < z then
      ENNReal.ofReal (z - t) * ENNReal.ofReal (Real.exp (-(φ * z)))
      else 0 ∂(X.ν.map (fun y : ℝ => -y))).toReal
  have hreg := gaussian_native_double_tail_kernel_full_regularity X φ hφ
  have hKi : Integrable K volume := by simpa [K] using hreg.1
  have hKzero (t : ℝ) (ht : t ≤ 0) : K t = 0 := by simp [K, not_lt.mpr ht]
  have hKpos (t : ℝ) : 0 ≤ K t := by
    by_cases ht : 0 < t
    · exact hreg.2.2.2 t ht
    · simpa [hKzero t (le_of_not_gt ht)]
  have hI (s : ℝ) (hs : 0 < s) : 0 ≤ (∫ t, Real.exp (-s * t) * K t) ∧
      (∫ t, Real.exp (-s * t) * K t) ≤ ∫ t, K t := by
    have hb (t : ℝ) : 0 ≤ Real.exp (-s * t) * K t ∧
        Real.exp (-s * t) * K t ≤ K t := by
      constructor
      · exact mul_nonneg (le_of_lt (Real.exp_pos _)) (hKpos t)
      · by_cases ht : 0 < t
        · have he : Real.exp (-s * t) ≤ 1 :=
            Real.exp_le_one_iff.mpr (by nlinarith [mul_pos hs ht])
          nlinarith [mul_nonneg (sub_nonneg.mpr he) (hKpos t)]
        · simp [hKzero t (le_of_not_gt ht)]
    have hmeas : AEStronglyMeasurable (fun t : ℝ => Real.exp (-s * t) * K t) volume :=
      (by fun_prop : Measurable (fun t : ℝ => Real.exp (-s * t))).aestronglyMeasurable.mul hKi.aestronglyMeasurable
    have hin : Integrable (fun t : ℝ => Real.exp (-s * t) * K t) volume := by
      apply hKi.mono hmeas
      filter_upwards with t
      have hh := hb t
      simpa only [Real.norm_eq_abs, abs_of_nonneg hh.1,
        abs_of_nonneg (hKpos t)] using hh.2
    exact ⟨integral_nonneg (fun t => (hb t).1),
      integral_mono hin hKi (fun t => (hb t).2)⟩
  have hid : Tendsto (fun s : ℝ => s) (nhdsWithin (0 : ℝ) (Ioi 0)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hterm : Tendsto (fun s : ℝ => s * (∫ t, Real.exp (-s * t) * K t))
      (nhdsWithin (0 : ℝ) (Ioi 0)) (𝓝 0) := by
    have ht : Tendsto (fun s : ℝ => s * (∫ t : ℝ, K t ∂volume))
        (nhdsWithin (0 : ℝ) (Ioi 0)) (𝓝 0) := by
      simpa only [zero_mul] using hid.mul_const (∫ t : ℝ, K t ∂volume)
    apply Filter.Tendsto.squeeze' tendsto_const_nhds ht
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact mul_nonneg (le_of_lt hs) (hI s hs).1
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact mul_le_mul_of_nonneg_left (hI s hs).2 (le_of_lt hs)
  have hsec (s : ℝ) (hs : 0 < s) : (X.ψ (φ + s) - X.ψ φ) / s =
      A + (X.σ ^ 2 / 2) * s + s * (∫ t, Real.exp (-s * t) * K t) := by
    rw [hroot]
    rw [gaussian_native_esscher_real_kernel_denominator X q φ s hφ hs hroot]
    dsimp [A, K]
    field_simp [ne_of_gt hs]
  have hsecT : Tendsto (fun s : ℝ => (X.ψ (φ + s) - X.ψ φ) / s) (nhdsWithin (0 : ℝ) (Ioi 0)) (𝓝 A) := by
    have hlin : Tendsto (fun s : ℝ => (X.σ ^ 2 / 2) * s)
        (nhdsWithin (0 : ℝ) (Ioi 0)) (𝓝 0) := by
      have hlim : Tendsto (fun s : ℝ => (X.σ ^ 2 / 2) * s)
          (nhdsWithin (0 : ℝ) (Ioi 0)) (𝓝 ((X.σ ^ 2 / 2) * 0)) :=
        tendsto_const_nhds.mul hid
      simpa only [mul_zero] using hlim
    have hconst : Tendsto (fun _ : ℝ => A) (nhdsWithin (0 : ℝ) (Ioi 0))
        (𝓝 A) := tendsto_const_nhds
    have ht : Tendsto (fun s : ℝ => A + (X.σ ^ 2 / 2) * s +
        s * (∫ t, Real.exp (-s * t) * K t)) (nhdsWithin (0 : ℝ) (Ioi 0))
        (𝓝 A) := by
      simpa only [add_zero] using (hconst.add hlin).add hterm
    apply ht.congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (hsec s hs).symm
  have hmT : Tendsto (fun s : ℝ => (X.ψ (φ + s) - X.ψ φ) / s) (nhdsWithin (0 : ℝ) (Ioi 0)) (𝓝 m) := by
    simpa [div_eq_mul_inv, smul_eq_mul, mul_comm] using hm.tendsto_slope_zero_right
  change m = A
  exact tendsto_nhds_unique hmT hsecT
