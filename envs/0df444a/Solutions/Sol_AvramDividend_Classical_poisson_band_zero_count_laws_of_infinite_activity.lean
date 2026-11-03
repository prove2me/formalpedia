-- Prove2me | solution 1 for AvramDividend.Classical.poisson_band_zero_count_laws_of_infinite_activity
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T11:57:08.275496+00:00
-- url     : https://prove2.me/submissions/aef9a9a3-c8b1-4dd7-9ece-542280dfb4ee
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Positivity
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_no_jump_probability

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Source negative-band count reduction on the original Lévy paths. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hTop : X.ν (Iio (0 : ℝ)) = ⊤)
    (δ : ℕ → ℝ≥0) :
    ∃ counts : ℕ → ℕ → Ω → ℕ,
      (∀ k n : ℕ,
        {ω : Ω | ¬ ∃ t : ℝ≥0, 0 < t ∧ t < δ k ∧
          ∃ l : ℝ, Tendsto (fun s : ℝ≥0 => X.X s ω)
            (nhdsWithin t (Iio t)) (nhds l) ∧ X.X t ω < l}
          ⊆ {ω | counts k n ω = 0}) ∧
      (∀ k n : ℕ,
        P {ω | counts k n ω = 0} =
          ENNReal.ofReal (Real.exp
            (-((δ k : ℝ) *
              (X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal)))) := by
  classical
  let qualifying : ℕ → ℕ → Ω → Prop := fun k n ω =>
    ∃ t : ℝ≥0, 0 < t ∧ t < δ k ∧
      ∃ l : ℝ, Tendsto (fun s : ℝ≥0 => X.X s ω)
        (nhdsWithin t (Iio t)) (nhds l) ∧
        X.X t ω + 1 / ((n : ℝ) + 1) ≤ l
  let counts : ℕ → ℕ → Ω → ℕ := fun k n ω =>
    if qualifying k n ω then 1 else 0
  refine ⟨counts, ?_, ?_⟩
  · intro k n ω hNo
    have hNot : ¬ qualifying k n ω := by
      intro hQ
      rcases hQ with ⟨t, ht0, htδ, l, hLim, hJump⟩
      have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      have hstrict : X.X t ω < l := by linarith
      exact hNo ⟨t, ht0, htδ, l, hLim, hstrict⟩
    simp [counts, hNot]
  · intro k n
    have hSet :
        {ω : Ω | counts k n ω = 0} =
          {ω : Ω | ¬ qualifying k n ω} := by
      ext ω
      by_cases h : qualifying k n ω
      · simp [counts, h]
      · simp [counts, h]
    rw [hSet]
    exact
      avram_wave7_06_original_negative_band_no_jump_probability X (δ k) n
