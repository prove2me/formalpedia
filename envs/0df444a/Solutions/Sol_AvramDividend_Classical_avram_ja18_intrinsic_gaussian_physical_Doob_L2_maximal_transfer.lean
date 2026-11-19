-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18_intrinsic_gaussian_physical_Doob_L2_maximal_transfer
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T22:46:02.60216+00:00
-- url     : https://prove2.me/submissions/4047f689-5179-4e7e-b3da-d5b4bcfa6150

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_a43_original_gaussian_continuous_raw_adapted_centered_martingale_indep_stationary_20261114
import Theorems.Thm_AvramDividend_Classical_avram_ga_a421_continuous_real_martingale_horizon_L2_maximal_integrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun j : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X j t ω)
        atTop (nhds (R t ω)))
    (n : ℕ) (hn : 0 < n)
    (hSquare : Integrable (fun ω => (R (n : ℝ≥0) ω) ^ 2) P) :
    ∃ B : Ω → ℝ,
      Integrable B P ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≤ (n : ℝ≥0) →
        ‖R t ω‖ ≤ B ω) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  obtain ⟨G, hMeas, hZero, hEq, hCont, hIndep, hStat, hInt, hCond⟩ :=
    avram_a43_original_gaussian_continuous_raw_adapted_centered_martingale_indep_stationary_20261114
      X hX hFinite R hR
  have hMart : Martingale G 𝓕.rightCont P := by
    constructor
    · intro t
      exact ((hMeas t).mono (𝓕.le_rightCont t) le_rfl).stronglyMeasurable
    · intro s t hst
      exact hCond s t hst
  have hGsq : Integrable (fun ω => (G (n : ℝ≥0) ω) ^ 2) P := by
    apply hSquare.congr
    filter_upwards [hEq] with ω hω
    exact congrArg (fun z : ℝ => z ^ 2) (hω (n : ℝ≥0)).symm
  obtain ⟨S, hSint, hS⟩ :=
    avram_ga_a421_continuous_real_martingale_horizon_L2_maximal_integrable
      P 𝓕.rightCont G hMart hCont (n : ℝ≥0) hGsq
  refine ⟨(fun ω => S ω + 1), hSint.add (integrable_const 1), ?_⟩
  filter_upwards [hS, hEq] with ω hSω hEqω
  intro t ht
  have hSq : (G t ω) ^ 2 ≤ S ω := hSω.2 t ht
  have hAbsSq : (|G t ω|) ^ 2 ≤ S ω := by
    simpa only [sq_abs] using hSq
  rw [← hEqω t, Real.norm_eq_abs]
  nlinarith [sq_nonneg (|G t ω| - 1), abs_nonneg (G t ω)]
