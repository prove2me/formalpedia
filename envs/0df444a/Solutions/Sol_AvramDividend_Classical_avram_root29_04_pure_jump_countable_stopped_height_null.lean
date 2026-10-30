-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_04_pure_jump_countable_stopped_height_null
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T10:01:16.803398+00:00
-- url     : https://prove2.me/submissions/fd96e8c8-f6c6-4d3f-8939-f2ad4c209183

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.OuterMeasure.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_root29_04_pure_jump_stopped_esscher_height_null

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

/-- A countable sequence of genuine stopped reflected excursion marks
cannot contain an exact positive (or zero) fixed height under a finite
Esscher probability when each mark has the certified hitting geometry. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hvar : (∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν) = ⊤)
    (θ : ℝ) (hθ : 0 ≤ θ) (T : ℝ≥0)
    (τ ζ Height : ℕ → Ω → ℝ≥0) (x : ℝ≥0)
    (hτ : ∀ k : ℕ, ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] {ω : Ω | τ k ω ≤ s})
    (hstop : ∀ k : ℕ,
      IsStoppingTime 𝓕 (fun ω => (τ k ω : WithTop ℝ≥0)))
    (hAtLevel : ∀ k : ℕ, ∀ ω : Ω, Height k ω = x →
      τ k ω < ζ k ω ∧
      reflectedSup X (τ k ω) ω = (x : ℝ) ∧
      ∀ t : ℝ≥0, τ k ω ≤ t → t < ζ k ω →
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
      (⋃ k : ℕ, {ω : Ω | Height k ω = x}) = 0 := by
  apply measure_iUnion_null
  intro k
  exact avram_root29_04_pure_jump_stopped_esscher_height_null
    X hvar θ hθ T (τ k) (hτ k) (hstop k) (ζ k)
    (Height k) x (hAtLevel k)
    times horizons hdense hpos hcofinal
