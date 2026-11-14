-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb24_original_finite_ruin_stopped_ENNReal_clock_eventually_inside_uniform_prefix
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T08:43:50.52022+00:00
-- url     : https://prove2.me/submissions/76714a97-0d0f-4f0b-8707-516802a48d73

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    (τ : ℝ≥0∞) (T : ℝ) (hT : 0 < T)
    (hτ : τ < ENNReal.ofReal T) :
    ∀ᶠ n : ℕ in atTop,
      τ < ENNReal.ofReal (T - T / ((n : ℝ) + 2))  := by
  have hFinite : τ ≠ ⊤ := by
    exact ne_of_lt (lt_of_lt_of_le hτ le_top)
  have hTop : ENNReal.ofReal T ≠ ⊤ := by simp
  have hReal : τ.toReal < T := by
    have h := (ENNReal.toReal_lt_toReal hFinite hTop).2 hτ
    simpa [ENNReal.toReal_ofReal hT.le] using h
  have hDelta : Tendsto (fun n : ℕ => T / ((n : ℝ) + 2))
      atTop (𝓝 (0 : ℝ)) := by
    have hShift :=
      (Filter.tendsto_add_atTop_iff_nat
        (f := fun k : ℕ => T / (k : ℝ))
        (l := 𝓝 (0 : ℝ)) 2).2
          (tendsto_const_div_atTop_nhds_zero_nat T)
    simpa [Nat.cast_add] using hShift
  have hPrefix : ∀ᶠ n : ℕ in atTop,
      τ.toReal < T - T / ((n : ℝ) + 2) := by
    have hTend : Tendsto (fun n : ℕ => T - T / ((n : ℝ) + 2))
        atTop (𝓝 T) := by
      simpa using (tendsto_const_nhds.sub hDelta)
    exact hTend.eventually (isOpen_Ioi.mem_nhds hReal)
  filter_upwards [hPrefix] with n hn
  have hCoerced :
      ENNReal.ofReal τ.toReal <
        ENNReal.ofReal (T - T / ((n : ℝ) + 2)) :=
    (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ENNReal.toReal_nonneg).2 hn
  simpa [ENNReal.ofReal_toReal hFinite] using hCoerced
