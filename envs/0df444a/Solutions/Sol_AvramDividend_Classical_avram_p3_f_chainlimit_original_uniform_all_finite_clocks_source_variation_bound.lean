-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_f_chainlimit_original_uniform_all_finite_clocks_source_variation_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T17:02:51.696198+00:00
-- url     : https://prove2.me/submissions/1c69175d-7466-4c16-a018-c20052e4221b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_removed_residual_monotone
import Theorems.Thm_AvramDividend_Classical_avram_p3_f_chainlimit_original_raw_J_monotone
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P,
      let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0
      let R : ℝ≥0 → ℝ := fun t =>
        ((t : ℝ) * X.drift - X.X t ω) - J t
      ∀ (τ : ℝ≥0) (u : ℕ → ℕ → ℝ≥0) (n : ℕ → ℕ)
        (hEnd : ∀ k, (u k) (n k) ≤ τ),
        ∃ M : ℝ, 0 ≤ M ∧ ∀ k,
          |X.drift| * (((u k) (n k) : ℝ) - ((u k) 0 : ℝ)) +
            (R ((u k) (n k)) - R ((u k) 0)) +
            (J ((u k) (n k)) - J ((u k) 0)) ≤ M := by
  classical
  filter_upwards
    [avram_p3_a_bvdrift_original_raw_removed_residual_monotone X hBV,
     avram_p3_f_chainlimit_original_raw_J_monotone X hBV]
      with ω hR hJ
  intro J R τ u n hEnd
  let M : ℝ := |X.drift| * (τ : ℝ) +
    (R τ - R 0) + (J τ - J 0)
  have hZeroClock : (0 : ℝ≥0) ≤ τ := by positivity
  have hR0 : R 0 ≤ R τ := hR hZeroClock
  have hJ0 : J 0 ≤ J τ := hJ 0 τ hZeroClock
  have hM0 : 0 ≤ M := by
    dsimp only [M]
    have hr := sub_nonneg.mpr hR0
    have hj := sub_nonneg.mpr hJ0
    have hprod : 0 ≤ |X.drift| * (τ : ℝ) := by positivity
    linarith
  refine ⟨M, hM0, ?_⟩
  intro k
  have hEndReal : ((u k) (n k) : ℝ) ≤ (τ : ℝ) := by
    exact_mod_cast hEnd k
  have hStartReal : 0 ≤ ((u k) 0 : ℝ) := by positivity
  have hTime : ((u k) (n k) : ℝ) - ((u k) 0 : ℝ) ≤
      (τ : ℝ) := by linarith
  have hRend : R ((u k) (n k)) ≤ R τ := hR (hEnd k)
  have hZeroStart : (0 : ℝ≥0) ≤ (u k) 0 := by positivity
  have hRstart : R 0 ≤ R ((u k) 0) := hR hZeroStart
  have hJend : J ((u k) (n k)) ≤ J τ :=
    hJ ((u k) (n k)) τ (hEnd k)
  have hJstart : J 0 ≤ J ((u k) 0) :=
    hJ 0 ((u k) 0) hZeroStart
  have hDrift : |X.drift| *
      (((u k) (n k) : ℝ) - ((u k) 0 : ℝ)) ≤
      |X.drift| * (τ : ℝ) :=
    mul_le_mul_of_nonneg_left hTime (abs_nonneg _)
  dsimp only [M]
  linarith
