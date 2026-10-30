-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_04_pure_jump_esscher_capped_posthit_regular
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T08:15:05.65612+00:00
-- url     : https://prove2.me/submissions/e4fd083d-ebf7-4329-bd57-b6465372a495

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_ae_rogozin_slopes_of_infinite_small_jumps
import Theorems.Thm_AvramDividend_Classical_ae_negative_near_zero_of_ae_rogozin_negative_slopes
import Theorems.Thm_AvramDividend_Classical_reflectedSup_capped_firstClosedHit_posthit_negative_of_regular_source
import Theorems.Thm_AvramDividend_Classical_ae_negative_near_zero_of_absolutelyContinuous

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

/-- Capped reflected first-hit posthit negativity survives
finite-clock Esscher weighting. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hvar : (∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν) = ⊤)
    (θ : ℝ) (hθ : 0 ≤ θ) (T H : ℝ≥0) (x : ℝ)
    (times horizons : ℕ → ℝ≥0)
    (hdense : ∀ a b : ℝ≥0, a < b →
      ∃ m : ℕ, a < times m ∧ times m < b)
    (hpos : ∀ n : ℕ, 0 < horizons n)
    (hcofinal : ∀ ε : ℝ≥0, 0 < ε →
      ∃ n : ℕ, horizons n ≤ ε) :
    ∀ᵐ ω ∂(P.withDensity (fun ω : Ω =>
      ENNReal.ofReal (Real.exp
        (θ * X.X T ω - (T : ℝ) * X.ψ θ)))),
      ∀ ε : ℝ≥0, 0 < ε →
        ∃ s : ℝ≥0, s < ε ∧
          X.X (sInf ((Icc (0 : ℝ≥0) H ∩
            (fun u : ℝ≥0 => reflectedSup X u ω) ⁻¹' Ici x) ∪ {H}) + s) ω -
          X.X (sInf ((Icc (0 : ℝ≥0) H ∩
            (fun u : ℝ≥0 => reflectedSup X u ω) ⁻¹' Ici x) ∪ {H})) ω < 0 := by
  have hSlope := ae_rogozin_slopes_of_infinite_small_jumps X hvar
  have hRegular : ∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
      ∃ s : ℝ≥0, s < ε ∧ X.X s ω < 0 :=
    ae_negative_near_zero_of_ae_rogozin_negative_slopes X hSlope
  have hPost :=
    reflectedSup_capped_firstClosedHit_posthit_negative_of_regular_source
      X H x times horizons hdense hpos hcofinal hRegular
  exact ae_negative_near_zero_of_absolutelyContinuous P
    (P.withDensity (fun ω : Ω =>
      ENNReal.ofReal (Real.exp
        (θ * X.X T ω - (T : ℝ) * X.ψ θ))))
    (fun s ω =>
      X.X (sInf ((Icc (0 : ℝ≥0) H ∩
        (fun u : ℝ≥0 => reflectedSup X u ω) ⁻¹' Ici x) ∪ {H}) + s) ω -
      X.X (sInf ((Icc (0 : ℝ≥0) H ∩
        (fun u : ℝ≥0 => reflectedSup X u ω) ⁻¹' Ici x) ∪ {H})) ω)
    (withDensity_absolutelyContinuous P _) hPost
