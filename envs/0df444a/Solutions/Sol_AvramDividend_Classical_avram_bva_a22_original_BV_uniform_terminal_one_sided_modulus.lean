-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva_a22_original_BV_uniform_terminal_one_sided_modulus
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T07:37:14.304143+00:00
-- url     : https://prove2.me/submissions/a0df83bb-9dd7-4941-aa66-9f75e1529d03

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_uniform_last_reserve_drift_upper
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_uniform_strict_mesh_cofinal_at_horizon
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (B : ℝ)
    (hmono : MonotoneOn w (Icc (0 : ℝ) B))
    (hmod : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ y ∈ Icc (0 : ℝ) B, ∀ z ∈ Icc (0 : ℝ) B,
      |z - y| < δ → |w z - w y| < ε)
    (T : ℝ) (hT : 0 < T) (u : ℕ → ℕ → ℝ≥0)
    (huniform : ∀ m i, (u m i : ℝ) =
      T * (i : ℝ) / ((m : ℝ) + 2)) :
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    ∀ ε : ℝ, 0 < ε → ∀ᶠ m in atTop,
      ∀ᵐ ω ∂P,
        (x + X.X (u m (m + 1)) ω -
          rightLimit D (u m (m + 1)) ω) ∈ Icc (0 : ℝ) B →
        (x + X.X S ω - rightLimit D S ω) ∈ Icc (0 : ℝ) B →
        w (x + X.X S ω - rightLimit D S ω) -
          w (x + X.X (u m (m + 1)) ω -
            rightLimit D (u m (m + 1)) ω) ≤ ε := by
  intro S ε hε
  obtain ⟨δ, hδ, hmodδ⟩ := hmod ε hε
  have hEnd :=
    (avram_p3_grid4_original_uniform_strict_mesh_cofinal_at_horizon
      T hT).2
  have hDelta : Tendsto (fun m : ℕ => T / ((m : ℝ) + 2))
      atTop (𝓝 (0 : ℝ)) := by
    have hSub : Tendsto (fun m : ℕ =>
        T - (T - T / ((m : ℝ) + 2))) atTop (𝓝 (T - T)) :=
      tendsto_const_nhds.sub hEnd
    simpa using hSub
  have hB : Tendsto (fun m : ℕ =>
      (T / ((m : ℝ) + 2)) * max X.drift 0)
      atTop (𝓝 (0 : ℝ)) := by
    simpa using hDelta.mul_const (max X.drift 0)
  have hSmall : ∀ᶠ (m : ℕ) in atTop,
      (T / ((m : ℝ) + 2)) * max X.drift 0 < δ := by
    have hmem : Set.Iio δ ∈ 𝓝 (0 : ℝ) := Iio_mem_nhds hδ
    simpa only [Set.mem_Iio] using hB.eventually hmem
  have hSource :=
    avram_bva_a22_original_uniform_last_reserve_drift_upper
      X hBV x D hD T hT u huniform
  filter_upwards [hSmall] with m hm
  filter_upwards [hSource] with ω hω
  intro hy hz
  let y := x + X.X (u m (m + 1)) ω -
    rightLimit D (u m (m + 1)) ω
  let z := x + X.X S ω - rightLimit D S ω
  have hzy : z - y ≤ (T / ((m : ℝ) + 2)) * max X.drift 0 :=
    hω m
  by_cases hle : z ≤ y
  · exact (sub_nonpos.mpr (hmono hz hy hle)).trans (le_of_lt hε)
  · have hyz : y < z := lt_of_not_ge hle
    have habs : |z - y| < δ := by
      rw [abs_of_nonneg (sub_nonneg.mpr (le_of_lt hyz))]
      exact lt_of_le_of_lt hzy hm
    exact (le_abs_self _).trans (le_of_lt (hmodδ y hy z hz habs))
