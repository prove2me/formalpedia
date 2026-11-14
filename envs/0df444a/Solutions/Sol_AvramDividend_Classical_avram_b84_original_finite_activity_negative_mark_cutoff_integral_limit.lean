-- Prove2me | solution 1 for AvramDividend.Classical.avram_b84_original_finite_activity_negative_mark_cutoff_integral_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T16:51:38.206206+00:00
-- url     : https://prove2.me/submissions/074d8ac1-50f6-423b-ac0b-3e7745f0a9b2

import Mathlib
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_b83_original_finite_negative_activity_small_mark_integrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Exact cofinal physical negative small-mark band exhaustion, independent of stochastic hypotheses. -/
private theorem avram_a22_local_negative_band_union :
    (⋃ n : ℕ, Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1)))) =
      Ioo (-1 : ℝ) 0 := by
  ext z
  simp only [Set.mem_iUnion, Set.mem_Ioc, Set.mem_Ioo]
  constructor
  · rintro ⟨n, hleft, hright⟩
    have hd : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := div_pos one_pos hd
    exact ⟨hleft, by linarith⟩
  · intro hz
    letI : Archimedean ℝ := Real.instArchimedean
    have hpos : (0 : ℝ) < -z := by linarith [hz.2]
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hpos
    refine ⟨n, hz.1, ?_⟩
    linarith

/-- The signed original finite-intensity small negative mark compensator converges. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    Tendsto (fun n : ℕ =>
      ∫ z in Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1))), z ∂X.ν)
      atTop (𝓝 (∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν)) := by
  let B : ℕ → Set ℝ :=
    fun n => Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1)))
  have hMono : Monotone B := by
    intro n m hnm z hz
    have hle : (n : ℝ) + 1 ≤ (m : ℝ) + 1 := by
      exact_mod_cast Nat.add_le_add_right hnm 1
    have hre : 1 / ((m : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) hle
    exact ⟨hz.1, hz.2.trans (by dsimp [B] at hz ⊢; linarith)⟩
  have hInt : IntegrableOn (fun z : ℝ => z) (⋃ n, B n) X.ν := by
    rw [show (⋃ n, B n) = Ioo (-1 : ℝ) 0 from
      avram_a22_local_negative_band_union]
    exact avram_b83_original_finite_negative_activity_small_mark_integrable
      X hFinite
  have ht := tendsto_setIntegral_of_monotone
    (μ := X.ν) (f := fun z : ℝ => z)
    (fun n => measurableSet_Ioc) hMono hInt
  change Tendsto (fun n : ℕ => ∫ z in B n, z ∂X.ν)
    atTop (𝓝 (∫ z in ⋃ n, B n, z ∂X.ν)) at ht
  simpa only [B, avram_a22_local_negative_band_union] using ht
