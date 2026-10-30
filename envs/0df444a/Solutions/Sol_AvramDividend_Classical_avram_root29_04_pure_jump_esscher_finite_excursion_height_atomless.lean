-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_04_pure_jump_esscher_finite_excursion_height_atomless
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T08:34:36.278421+00:00
-- url     : https://prove2.me/submissions/64eeb42a-0093-4b8e-9609-ca49820c3b01

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_ae_rogozin_slopes_of_infinite_small_jumps
import Theorems.Thm_AvramDividend_Classical_ae_negative_near_zero_of_ae_rogozin_negative_slopes
import Theorems.Thm_AvramDividend_Classical_reflectedSup_finite_excursion_height_level_null_under_P_of_regular

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

/-- Finite excursions of the original process have atomless fixed positive
height also under the genuine finite-clock Esscher weighted law. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hvar : (∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν) = ⊤)
    (θ : ℝ) (hθ : 0 ≤ θ) (T H : ℝ≥0) (hH : 0 < H)
    (Height : Ω → ℝ≥0) (x : ℝ≥0) (hx : 0 < x)
    (hHeight : ∀ ω : Ω, Height ω = x →
      reflectedSup X H ω = 0 ∧
      sSup ((fun u : ℝ≥0 => reflectedSup X u ω) '' Icc 0 H) = (x : ℝ))
    (times horizons : ℕ → ℝ≥0)
    (hdense : ∀ a b : ℝ≥0, a < b →
      ∃ m : ℕ, a < times m ∧ times m < b)
    (hpos : ∀ n : ℕ, 0 < horizons n)
    (hcofinal : ∀ ε : ℝ≥0, 0 < ε →
      ∃ n : ℕ, horizons n ≤ ε) :
    (P.withDensity (fun ω : Ω =>
      ENNReal.ofReal (Real.exp
        (θ * X.X T ω - (T : ℝ) * X.ψ θ))))
      {ω : Ω | Height ω = x} = 0 := by
  have hSlope := ae_rogozin_slopes_of_infinite_small_jumps X hvar
  have hRegular : ∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
      ∃ s : ℝ≥0, s < ε ∧ X.X s ω < 0 :=
    ae_negative_near_zero_of_ae_rogozin_negative_slopes X hSlope
  have hNullP : P {ω : Ω | Height ω = x} = 0 :=
    reflectedSup_finite_excursion_height_level_null_under_P_of_regular
      X H hH Height x hx hHeight times horizons
      hdense hpos hcofinal hRegular
  exact (withDensity_absolutelyContinuous P
    (fun ω : Ω => ENNReal.ofReal (Real.exp
      (θ * X.X T ω - (T : ℝ) * X.ψ θ)))) hNullP
