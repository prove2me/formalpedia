-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_workerC_original_preterminal_uniform_grid_precontact_times
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T08:40:50.911268+00:00
-- url     : https://prove2.me/submissions/1041cfd8-0857-46d4-93df-54915267d83f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (ρ : Ω → ℝ≥0)
    (hρruin : ∀ ω, (ρ ω : ℝ≥0∞) ≤ ruinTime X x D ω)
    (k : ℕ) (hk : 0 < k) :
    let A : Ω → Finset ℝ≥0 := fun ω =>
      (Finset.range k).image
        (fun i : ℕ => ρ ω * ((i : ℝ≥0) / (k : ℝ≥0)))
    ∀ ω t, t ∈ A ω →
      t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω := by
  intro A ω t ht
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ht
  have hifin : i < k := Finset.mem_range.mp hi
  by_cases hzero : ρ ω = 0
  · left
    simp [hzero]
  · right
    have hkpos : (0 : ℝ≥0) < k := by exact_mod_cast hk
    have hifrac : ((i : ℝ≥0) / (k : ℝ≥0)) < 1 := by
      apply (div_lt_iff₀ hkpos).2
      simpa using hifin
    have hρpos : (0 : ℝ≥0) < ρ ω := pos_iff_ne_zero.mpr hzero
    have hlt : ρ ω * ((i : ℝ≥0) / (k : ℝ≥0)) < ρ ω := by
      exact (mul_lt_mul_of_pos_left hifrac hρpos).trans_eq (mul_one _)
    exact (ENNReal.coe_lt_coe.mpr hlt).trans_le (hρruin ω)

