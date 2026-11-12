-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18g_original_psi_small_large_integral_split
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T08:12:37.132388+00:00
-- url     : https://prove2.me/submissions/523b93ed-af75-482c-a10c-6556de7304c7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_exp_compensated_jump_integrable_levy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Split the original Lévy-Khintchine integral at the negative unit jump. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (θ : ℝ) (hθ : 0 ≤ θ) :
    X.ψ θ =
      X.c * θ + X.σ ^ 2 * θ ^ 2 / 2 +
      (∫ z in Ioo (-1 : ℝ) 0,
        Real.exp (θ * z) - 1 - θ * z ∂X.ν) +
      (∫ z in Iic (-1 : ℝ), Real.exp (θ * z) - 1 ∂X.ν) := by
  let S : Set ℝ := Ioo (-1 : ℝ) 0
  let B : Set ℝ := Iic (-1 : ℝ)
  let f : ℝ → ℝ := fun z =>
    Real.exp (θ * z) - 1 -
      θ * z * (Ioo (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ)) z
  have hfi : IntegrableOn f (Iio (0 : ℝ)) X.ν := by
    exact exp_compensated_jump_integrable_levy X θ hθ
  have hSsub : S ⊆ Iio (0 : ℝ) := fun z hz => hz.2
  have hBsub : B ⊆ Iio (0 : ℝ) := by
    intro z hz
    change z ≤ (-1 : ℝ) at hz
    exact lt_of_le_of_lt hz (by norm_num)
  have hS : IntegrableOn f S X.ν := hfi.mono_set hSsub
  have hB : IntegrableOn f B X.ν := hfi.mono_set hBsub
  have hdis : Disjoint S B := by
    apply disjoint_left.mpr
    intro z hzS hzB
    change z ≤ (-1 : ℝ) at hzB
    exact (not_le_of_gt hzS.1) hzB
  have hun : S ∪ B = Iio (0 : ℝ) := by
    ext z
    simp only [S, B, mem_union, mem_Ioo, mem_Iic, mem_Iio]
    constructor
    · rintro (h | h)
      · exact h.2
      · exact lt_of_le_of_lt h (by norm_num)
    · intro hz
      by_cases h : z ≤ -1
      · exact Or.inr h
      · exact Or.inl ⟨lt_of_not_ge h, hz⟩
  have hsplit :
      (∫ z in Iio (0 : ℝ), f z ∂X.ν) =
        (∫ z in S, f z ∂X.ν) + (∫ z in B, f z ∂X.ν) := by
    rw [← hun]
    exact setIntegral_union hdis measurableSet_Iic hS hB
  have hs : (∫ z in S, f z ∂X.ν) =
      (∫ z in S, Real.exp (θ * z) - 1 - θ * z ∂X.ν) := by
    apply setIntegral_congr_fun measurableSet_Ioo
    intro z hz
    have hm : z ∈ Ioo (-1 : ℝ) 1 :=
      ⟨hz.1, lt_trans hz.2 (by norm_num)⟩
    simp [f, Set.indicator_of_mem hm]
  have hb : (∫ z in B, f z ∂X.ν) =
      (∫ z in B, Real.exp (θ * z) - 1 ∂X.ν) := by
    apply setIntegral_congr_fun measurableSet_Iic
    intro z hz
    change z ≤ (-1 : ℝ) at hz
    have hn : z ∉ Ioo (-1 : ℝ) 1 :=
      fun hh => (not_le_of_gt hh.1) hz
    simp [f, Set.indicator_of_notMem hn]
  change X.c * θ + X.σ ^ 2 * θ ^ 2 / 2 +
      (∫ z in Iio (0 : ℝ), f z ∂X.ν) = _
  rw [hsplit, hs, hb]
  ring
