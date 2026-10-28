-- Prove2me | solution 1 for CountingMatroid.Analysis.RelativeObservationBounds.learned_multiplier_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T14:06:19.491244+00:00
-- url     : https://prove2.me/submissions/15268b89-9c56-4e22-b5dd-953eb7fa2056

import Definitions.Def_CountingMatroid_Analysis_RelativeObservationBounds
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic
import Theorems.Thm_CountingMatroid_Analysis_RelativeObservationBounds_relative_quotient_bounds

set_option autoImplicit false

namespace CountingMatroid.Analysis.RelativeObservationBounds
end CountingMatroid.Analysis.RelativeObservationBounds
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.RelativeObservationBounds

/-- PAPER: main.tex:1257-1270
Accurate empirical type means estimate the current ideal multiplier within
factor two. The factor-two drift then gives a factor-four good multiplier
at the next parameter. -/
theorem solution (η w p₀ pᵢ x y ideal nextIdeal : ℚ)
    (hη : 0 ≤ η) (hηsmall : η ≤ 1 / 3)
    (hw : 0 < w) (hp₀ : 0 < p₀) (hpᵢ : 0 < pᵢ)
    (hx : RelativeEstimate η p₀ x) (hy : RelativeEstimate η pᵢ y)
    (hideal : w * p₀ / pᵢ = ideal)
    (hdrift : ideal / 2 ≤ nextIdeal ∧ nextIdeal ≤ 2 * ideal) :
    nextIdeal / 4 ≤ w * x / y ∧ w * x / y ≤ 4 * nextIdeal := by
  have hηlt : η < 1 := by linarith
  obtain ⟨hxp, hyp, hl, hu⟩ :=
    relative_quotient_bounds η p₀ pᵢ x y hη hηlt hp₀ hpᵢ hx hy
  have hidealpos : 0 < ideal := hideal ▸ div_pos (mul_pos hw hp₀) hpᵢ
  have hsame : (w * x / y) / ideal = (x / y) / (p₀ / pᵢ) := by
    rw [← hideal]
    field_simp
  rw [← hsame] at hl hu
  have hhalf : (1 / 2 : ℚ) ≤ (1 - η) / (1 + η) := by
    apply (le_div_iff₀ (by linarith : 0 < 1 + η)).mpr
    linarith
  have htwo : (1 + η) / (1 - η) ≤ (2 : ℚ) := by
    apply (div_le_iff₀ (by linarith : 0 < 1 - η)).mpr
    linarith
  have hlo := (le_div_iff₀ hidealpos).mp (hhalf.trans hl)
  have hup := (div_le_iff₀ hidealpos).mp (hu.trans htwo)
  constructor <;> linarith [hdrift.1, hdrift.2]
