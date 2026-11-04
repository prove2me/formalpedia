-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_g_radon_negative_band_finite_implies_locally_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T13:13:06.322089+00:00
-- url     : https://prove2.me/submissions/28dbe0b8-da19-445b-9655-ae219175f423

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped ENNReal

/-- Every negative point has a finite-mass neighbourhood, provided the
    negative mark measure is finite on every band separated from zero. -/
theorem solution
    (μ : Measure {x : ℝ // x < 0})
    (hBand : ∀ (ε : ℝ), 0 < ε →
      μ {x : {x : ℝ // x < 0} | (x : ℝ) ≤ -ε} < ⊤) :
    IsLocallyFiniteMeasure μ := by
  classical
  refine ⟨fun x => ?_⟩
  let ε : ℝ := -(x : ℝ) / 2
  have hε : 0 < ε := by
    dsimp [ε]
    linarith [x.property]
  have hx : (x : ℝ) < -ε := by
    dsimp [ε]
    linarith [x.property]
  let U : Set {y : ℝ // y < 0} := {y | (y : ℝ) < -ε}
  have hUopen : IsOpen U := by
    change IsOpen ((Subtype.val : {y : ℝ // y < 0} → ℝ) ⁻¹' Iio (-ε))
    exact isOpen_Iio.preimage continuous_subtype_val
  have hUmem : x ∈ U := hx
  have hUsub : U ⊆ {y : {y : ℝ // y < 0} | (y : ℝ) ≤ -ε} := by
    intro y hy
    change (y : ℝ) < -ε at hy
    exact le_of_lt hy
  have hUfinite : μ U < ⊤ :=
    lt_of_le_of_lt (measure_mono hUsub) (hBand ε hε)
  exact ⟨U, hUopen.mem_nhds hUmem, hUfinite⟩
