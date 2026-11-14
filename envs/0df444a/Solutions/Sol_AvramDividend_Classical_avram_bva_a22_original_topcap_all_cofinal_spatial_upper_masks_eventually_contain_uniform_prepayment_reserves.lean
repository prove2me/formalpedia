-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva_a22_original_topcap_all_cofinal_spatial_upper_masks_eventually_contain_uniform_prepayment_reserves
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T10:57:00.090479+00:00
-- url     : https://prove2.me/submissions/1a7405cb-3327-46b6-b2d7-e793884a4e3d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb_topcap_original_prejump_reserve_uniform_horizon_upper
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation) (x : ℝ) (C : ℝ≥0∞)
    (hTop : C = ⊤) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D) (S : ℝ≥0)
    (a b : ℕ → ℝ)
    (hcover : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      ∃ N : ℕ, ∀ n ≥ N, y ∈ Icc (a n) (b n)) :
    ∀ᶠ n : ℕ in atTop, ∀ᵐ ω ∂P,
      ∀ t : ℝ≥0, t ≤ S →
        Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s ω - rightLimit D s ω) t ≤ b n := by
  let B : ℝ := max (x + max ((S : ℝ) * X.drift) 0) 0
  let y : ℝ := max 1 (B + 1)
  have hypos : 0 < y :=
    lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hycap : ENNReal.ofReal y < C := by
    simp [hTop]
  obtain ⟨N, hN⟩ := hcover y hypos hycap
  have hUpper :=
    avram_bvb_topcap_original_prejump_reserve_uniform_horizon_upper
      X hBV x D hD.1.1 S
  filter_upwards [eventually_ge_atTop N] with n hn
  filter_upwards [hUpper] with ω hω
  intro t ht
  have hBy : B ≤ y := by
    dsimp [y]
    have hh : B ≤ B + 1 := by linarith
    exact le_trans hh (le_max_right _ _)
  exact (hω t ht).trans (hBy.trans (hN n hn).2)
