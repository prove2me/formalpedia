-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_04_pure_jump_stopped_esscher_height_null
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T09:44:35.725848+00:00
-- url     : https://prove2.me/submissions/6be1f298-27d9-4fd8-8c68-ae4ad8d887ce

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_root29_04_pure_jump_esscher_arbitrary_stopping_downward_regular
import Theorems.Thm_AvramDividend_Classical_reflectedSup_height_level_null_of_ae_posthit_negative

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

/-- An actual finite-terminal Esscher law has no exact excursion height
when the height is reached at a genuine stopping time. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hvar : (∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν) = ⊤)
    (θ : ℝ) (hθ : 0 ≤ θ) (T : ℝ≥0)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕 s] {ω : Ω | τ ω ≤ s})
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (ζ Height : Ω → ℝ≥0) (x : ℝ≥0)
    (hAtLevel : ∀ ω : Ω, Height ω = x →
      τ ω < ζ ω ∧
      reflectedSup X (τ ω) ω = (x : ℝ) ∧
      ∀ t : ℝ≥0, τ ω ≤ t → t < ζ ω →
        reflectedSup X t ω ≤ (x : ℝ))
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
  have hReg :=
    avram_root29_04_pure_jump_esscher_arbitrary_stopping_downward_regular
      X hvar θ hθ T τ hτ hstop times horizons hdense hpos hcofinal
  apply reflectedSup_height_level_null_of_ae_posthit_negative
    X (P.withDensity (fun ω : Ω =>
      ENNReal.ofReal (Real.exp
        (θ * X.X T ω - (T : ℝ) * X.ψ θ))))
    τ ζ Height x hAtLevel
  filter_upwards [hReg] with ω hw
  intro _ ε hε
  obtain ⟨s, hs, hneg⟩ := hw ε hε
  exact ⟨s, hs, by linarith⟩
