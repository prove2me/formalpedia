-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_a_zero_rate_original_exact_significant_jump_grid_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T00:25:52.317467+00:00
-- url     : https://prove2.me/submissions/486a591b-f467-44f0-af5e-1a602b3b8add

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_finite_significant_jump_finset
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_leftLim_origin_nnreal
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_positive_horizon_to_closed_significant_jumps
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_cadlag_regular_all_times
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_uniform_full_grid_compact_test_limit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal

/-- The genuine original-path grid limit uses exactly the positive-time
significant jumps, including the zero-origin boundary check. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (T : ℝ≥0) (hT : 0 < T)
    (ρ : ℝ) (hρ : 0 < ρ)
    (f : ℝ → ℝ) (hf : Continuous f)
    (hvanish : ∀ z : ℝ, |z| < ρ → f z = 0) :
    ∃ F : Finset ℝ≥0,
      (∀ t : ℝ≥0, t ∈ F ↔ 0 < t ∧ t ≤ T ∧
        ρ ≤ |X.X t ω -
          Function.leftLim (fun u : ℝ≥0 => X.X u ω) t|) ∧
      Tendsto (fun n : ℕ =>
        ∑ i ∈ Finset.range (n + 1),
          f (X.X (((i + 1 : ℕ) : ℝ≥0) *
              (T / ((n : ℝ≥0) + 1))) ω -
            X.X ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω))
        atTop (𝓝 (∑ t ∈ F,
          f (X.X t ω -
            Function.leftLim (fun u : ℝ≥0 => X.X u ω) t))) := by
  obtain ⟨F, hF⟩ :=
    avram_p2_a_zero_rate_original_finite_significant_jump_finset
      X ω T ρ hρ
  have hzero : X.X 0 ω =
      Function.leftLim (fun u : ℝ≥0 => X.X u ω) 0 :=
    (avram_p2_a_zero_rate_leftLim_origin_nnreal
      (fun u : ℝ≥0 => X.X u ω)).symm
  have hFoc : ∀ t ∈ Ioc (0 : ℝ≥0) T,
      ρ ≤ |X.X t ω -
        Function.leftLim (fun u : ℝ≥0 => X.X u ω) t| →
      t ∈ F := by
    intro t ht hr
    exact (hF t).2 ⟨ht.1, ht.2, hr⟩
  have hFcover : ∀ t ∈ Icc (0 : ℝ≥0) T,
      ρ ≤ |X.X t ω -
        Function.leftLim (fun u : ℝ≥0 => X.X u ω) t| →
      t ∈ F :=
    avram_p2_a_zero_rate_positive_horizon_to_closed_significant_jumps
      (fun u : ℝ≥0 => X.X u ω) T ρ hρ hzero F hFoc
  have hFpos : ∀ t ∈ F, 0 < t := by
    intro t ht
    exact ((hF t).1 ht).1
  have hFbound : ∀ t ∈ F, t ≤ T := by
    intro t ht
    exact ((hF t).1 ht).2.1
  obtain ⟨hL, hR⟩ :=
    avram_p2_a_zero_rate_original_cadlag_regular_all_times X ω
  refine ⟨F, hF, ?_⟩
  exact avram_p2_a_zero_rate_original_uniform_full_grid_compact_test_limit
    (fun u : ℝ≥0 => X.X u ω) T hT hL hR ρ hρ
    F hFcover hFpos hFbound f hf hvanish
