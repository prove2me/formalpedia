-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_fin13_original_finite_activity_truncated_residual_uniform_cauchy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T00:50:52.239968+00:00
-- url     : https://prove2.me/submissions/ef8690bf-2bd0-425e-9b18-28e141bab83e

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_ubv_mixed13_original_finite_activity_uniform_negative_mark_void_ae
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin13_original_finite_activity_void_annulus_truncated_residual_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ᵐ ω ∂P, ∀ (T : ℝ≥0) (ε : ℝ), 0 < ε →
      ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → n ≤ m →
        ∀ t : ℝ≥0, t ≤ T →
          |avram_p4_h_gaussian_intrinsic_truncated_residual X m t ω -
             avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω| < ε := by
  filter_upwards
      [avram_ubv_mixed13_original_finite_activity_uniform_negative_mark_void_ae
        X hFinite] with ω hω
  intro T ε hε
  obtain ⟨δ, hδ, hVoid⟩ := hω T
  let rateFinite : ℝ := (X.ν (Iio (0 : ℝ))).toReal
  have hrateFinite : 0 ≤ rateFinite := ENNReal.toReal_nonneg
  let K : ℝ := 1 + (T : ℝ) * rateFinite
  have hK : 0 < K := by dsimp [K]; positivity
  have hCutPos : 0 < min δ (ε / K) := lt_min hδ (div_pos hε hK)
  have hTend : Tendsto (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1))
      atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hEventually : ∀ᶠ k : ℕ in atTop,
      (1 : ℝ) / ((k : ℝ) + 1) < min δ (ε / K) :=
    hTend.eventually (eventually_lt_nhds hCutPos)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hEventually
  refine ⟨N, ?_⟩
  intro n m hn hnm t ht
  have hCut := hN n hn
  have hδn : (1 : ℝ) / ((n : ℝ) + 1) < δ :=
    lt_of_lt_of_le hCut (min_le_left _ _)
  have hεn : (1 : ℝ) / ((n : ℝ) + 1) < ε / K :=
    lt_of_lt_of_le hCut (min_le_right _ _)
  let B : Set ℝ := Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
  have hBsub : B ⊆ Ioo (-δ) 0 := by
    intro z hz
    change -(1 / ((n : ℝ) + 1)) < z ∧
      z ≤ -(1 / ((m : ℝ) + 1)) at hz
    change -δ < z ∧ z < 0
    constructor
    · linarith
    · have hmpos : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
      linarith
  let NX : Measure (ℝ≥0 × ℝ) :=
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  have hVoidT : NX (Ioc 0 T ×ˢ B) = 0 :=
    hVoid B measurableSet_Ioc hBsub
  have hIncl : (Ioc 0 t ×ˢ B) ⊆ (Ioc 0 T ×ˢ B) := by
    rintro ⟨s,z⟩ ⟨⟨hs0,hst⟩,hz⟩
    exact ⟨⟨hs0, le_trans hst ht⟩, hz⟩
  have hVoidt : NX (Ioc 0 t ×ˢ B) = 0 := by
    have hm := measure_mono hIncl (μ := NX)
    rw [hVoidT] at hm
    exact le_antisymm hm bot_le
  have hBound :=
    avram_mix_fin13_original_finite_activity_void_annulus_truncated_residual_bound
      X hFinite n m hnm t ω hVoidt
  have htn : (t : ℝ) ≤ (T : ℝ) := by exact_mod_cast ht
  have hrate : 0 ≤ ((1 : ℝ) / ((n : ℝ) + 1)) * rateFinite :=
    mul_nonneg (by positivity) hrateFinite
  have hKbound : (T : ℝ) * rateFinite ≤ K := by dsimp [K]; linarith
  have hFinal : (T : ℝ) * ((1 / ((n : ℝ) + 1)) * rateFinite) < ε := by
    calc
      (T : ℝ) * ((1 / ((n : ℝ) + 1)) * rateFinite) =
        (1 / ((n : ℝ) + 1)) * ((T : ℝ) * rateFinite) := by ring
      _ ≤ (1 / ((n : ℝ) + 1)) * K :=
        mul_le_mul_of_nonneg_left hKbound (by positivity)
      _ < (ε / K) * K := mul_lt_mul_of_pos_right hεn hK
      _ = ε := by field_simp [ne_of_gt hK]
  exact lt_of_le_of_lt
    (le_trans hBound (mul_le_mul_of_nonneg_right htn hrate)) hFinal
