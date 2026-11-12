-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva20_uniform_floor_index_within_inner_row
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T20:31:59.30644+00:00
-- url     : https://prove2.me/submissions/65c960b6-1448-4f99-ac3a-66facb2aaa47

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
noncomputable section

/-- The uniform floor index is a valid strict inner-horizon grid cell. -/
theorem solution
    (T : ℝ) (hT : 0 < T) (n : ℕ) (r : ℝ)
    (hr : 0 ≤ r)
    (hrT : r < T * ((n : ℝ) + 1) / ((n : ℝ) + 2)) :
    ⌊(r / T) * ((n : ℝ) + 2)⌋₊ < n + 1 := by
  have hden : 0 < (n : ℝ) + 2 := by positivity
  have hmul : r * ((n : ℝ) + 2) < T * ((n : ℝ) + 1) :=
    (lt_div_iff₀ hden).mp hrT
  have hscaled : (r / T) * ((n : ℝ) + 2) < ((n : ℝ) + 1) := by
    calc
      (r / T) * ((n : ℝ) + 2) =
          (r * ((n : ℝ) + 2)) / T := by ring
      _ < ((n : ℝ) + 1) := by
        apply (div_lt_iff₀ hT).mpr
        calc
          r * ((n : ℝ) + 2) < T * ((n : ℝ) + 1) := hmul
          _ = ((n : ℝ) + 1) * T := mul_comm _ _
  have hnonneg : 0 ≤ (r / T) * ((n : ℝ) + 2) :=
    mul_nonneg (div_nonneg hr hT.le) hden.le
  have hfloor :
      (⌊(r / T) * ((n : ℝ) + 2)⌋₊ : ℝ) ≤
        (r / T) * ((n : ℝ) + 2) := Nat.floor_le hnonneg
  have hcast : (⌊(r / T) * ((n : ℝ) + 2)⌋₊ : ℝ) < ((n : ℝ) + 1) :=
    lt_of_le_of_lt hfloor hscaled
  exact_mod_cast hcast
