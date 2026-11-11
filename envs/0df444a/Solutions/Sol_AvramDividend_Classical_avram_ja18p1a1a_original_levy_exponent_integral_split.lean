-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18p1a1a_original_levy_exponent_integral_split
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T02:13:43.460244+00:00
-- url     : https://prove2.me/submissions/12761ac4-b2f9-4ce8-85a8-4bbad6c279f9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_compensated_jump_integrable_nonneg

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Split the original compensated Levy exponent into disjoint small and large negative bands. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ) :
    (∫ z in Iio (0 : ℝ),
      (Real.exp (θ * z) - 1 -
        θ * z * (Ioo (-1 : ℝ) 1).indicator 1 z) ∂X.ν) =
      (∫ z in Ioo (-1 : ℝ) 0,
        (Real.exp (θ * z) - 1 - θ * z) ∂X.ν) +
      (∫ z in Iic (-1 : ℝ),
        (Real.exp (θ * z) - 1) ∂X.ν) := by
  let S : Set ℝ := Ioo (-1 : ℝ) 0
  let B : Set ℝ := Iic (-1 : ℝ)
  let f : ℝ → ℝ := fun z =>
    Real.exp (θ * z) - 1 -
      θ * z * (Ioo (-1 : ℝ) 1).indicator 1 z
  have hSIio : S ⊆ Iio (0 : ℝ) := fun z hz => hz.2
  have hBIio : B ⊆ Iio (0 : ℝ) := by
    intro z hz
    change z ≤ (-1 : ℝ) at hz
    exact lt_of_le_of_lt hz (by norm_num)
  have hInt : IntegrableOn f (Iio (0 : ℝ)) X.ν := by
    change IntegrableOn (fun z : ℝ =>
      Real.exp (θ * z) - 1 -
        θ * z * (Ioo (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) z)
      (Iio (0 : ℝ)) X.ν
    exact levy_compensated_jump_integrable_nonneg X θ hθ
  have hSInt : IntegrableOn f S X.ν := hInt.mono_set hSIio
  have hBInt : IntegrableOn f B X.ν := hInt.mono_set hBIio
  have hSmall :
      (∫ z in S, f z ∂X.ν) =
        (∫ z in S, Real.exp (θ * z) - 1 - θ * z ∂X.ν) := by
    apply integral_congr_ae
    exact ae_restrict_of_forall_mem measurableSet_Ioo (fun z hz => by
      have hm : z ∈ Ioo (-1 : ℝ) 1 :=
        ⟨hz.1, by linarith [hz.2]⟩
      simp [f, Set.indicator_of_mem hm])
  have hBig :
      (∫ z in B, f z ∂X.ν) =
        (∫ z in B, Real.exp (θ * z) - 1 ∂X.ν) := by
    apply integral_congr_ae
    exact ae_restrict_of_forall_mem measurableSet_Iic (fun z hz => by
      have hm : z ∉ Ioo (-1 : ℝ) 1 := by
        intro hm
        exact (not_lt_of_ge hz) hm.1
      simp [f, Set.indicator_of_notMem hm])
  have hDisjoint : Disjoint S B := by
    apply Set.disjoint_left.mpr
    intro z hzS hzB
    exact (not_lt_of_ge hzB) hzS.1
  have hUnion : S ∪ B = Iio (0 : ℝ) := by
    ext z
    simp only [S, B, mem_union, mem_Ioo, mem_Iic, mem_Iio]
    constructor
    · intro h
      rcases h with h | h
      · exact h.2
      · exact lt_of_le_of_lt h (by norm_num)
    · intro hz
      by_cases h : z ≤ -1
      · exact Or.inr h
      · exact Or.inl ⟨lt_of_not_ge h, hz⟩
  change (∫ z in Iio (0 : ℝ), f z ∂X.ν) = _
  calc
    (∫ z in Iio (0 : ℝ), f z ∂X.ν) =
        (∫ z in S ∪ B, f z ∂X.ν) := by rw [hUnion]
    _ = (∫ z in S, f z ∂X.ν) + (∫ z in B, f z ∂X.ν) :=
      setIntegral_union hDisjoint measurableSet_Iic hSInt hBInt
    _ = _ := by rw [hSmall, hBig]
