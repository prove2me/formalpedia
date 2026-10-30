-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_01_purejump_allFiniteHorizon_height_atomless
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T00:18:35.048984+00:00
-- url     : https://prove2.me/submissions/4ac27e23-7316-4067-8e39-8c00426f9a5d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_uniform_bounded_height_atomless
import Theorems.Thm_AvramDividend_Classical_ae_rogozin_slopes_of_infinite_small_jumps
import Theorems.Thm_AvramDividend_Classical_ae_negative_near_zero_of_ae_rogozin_negative_slopes

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

/-- Infinite small-jump variation excludes exact positive reflected maxima
at every finite terminal horizon, including random horizons. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ≥0) (hx : 0 < x)
    (times horizons : ℕ → ℝ≥0)
    (hdense : ∀ a b : ℝ≥0, a < b →
      ∃ m : ℕ, a < times m ∧ times m < b)
    (hpos : ∀ n : ℕ, 0 < horizons n)
    (hcofinal : ∀ ε : ℝ≥0, 0 < ε →
      ∃ n : ℕ, horizons n ≤ ε)
    (hjump : (∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν) = ⊤) :
    P {ω : Ω | ∃ H : ℝ≥0,
      sSup ((fun t : ℝ≥0 => reflectedSup X t ω) '' Icc 0 H) = (x : ℝ) ∧
      reflectedSup X H ω < (x : ℝ)} = 0 := by
  have hSlope := ae_rogozin_slopes_of_infinite_small_jumps X hjump
  have hRegular :=
    ae_negative_near_zero_of_ae_rogozin_negative_slopes X hSlope
  have hCap (n : ℕ) :
      P {ω : Ω | ∃ H : ℝ≥0, H ≤ (n : ℝ≥0) ∧
        sSup ((fun t : ℝ≥0 => reflectedSup X t ω) '' Icc 0 H) = (x : ℝ) ∧
        reflectedSup X H ω < (x : ℝ)} = 0 :=
    avram_wave3_01_uniform_bounded_height_atomless X (n : ℝ≥0) x hx
      times horizons hdense hpos hcofinal hRegular
  have hAE (n : ℕ) :
      ∀ᵐ ω ∂P, ω ∉ {ω : Ω | ∃ H : ℝ≥0, H ≤ (n : ℝ≥0) ∧
        sSup ((fun t : ℝ≥0 => reflectedSup X t ω) '' Icc 0 H) = (x : ℝ) ∧
        reflectedSup X H ω < (x : ℝ)} :=
    (measure_eq_zero_iff_ae_notMem).mp (hCap n)
  have hAll : ∀ᵐ ω ∂P, ∀ n : ℕ,
      ω ∉ {ω : Ω | ∃ H : ℝ≥0, H ≤ (n : ℝ≥0) ∧
        sSup ((fun t : ℝ≥0 => reflectedSup X t ω) '' Icc 0 H) = (x : ℝ) ∧
        reflectedSup X H ω < (x : ℝ)} :=
    ae_all_iff.mpr hAE
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [hAll] with ω hω
  rintro ⟨H, hMax, hEnd⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (H : ℝ)
  have hHN : H ≤ (n : ℝ≥0) := by exact_mod_cast hn.le
  exact hω n ⟨H, hHN, hMax, hEnd⟩
