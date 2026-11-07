-- Prove2me | solution 1 for AvramDividend.Classical.avram_a19_uniform_delta_profile
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T09:36:51.637226+00:00
-- url     : https://prove2.me/submissions/bc9e217e-e4d9-493a-b90e-71f27f1dd9e0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The physical uniform mesh has a positive, decreasing and vanishing
    terminal gap, which permits reuse of the stopped cash-prefix theorem. -/
theorem solution (T : ℝ) (hT : 0 < T) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    (∀ n, 0 < δ n) ∧ (∀ n, δ n ≤ T) ∧
    Antitone δ ∧ Tendsto δ atTop (nhds (0 : ℝ)) := by
  dsimp
  have hpos : ∀ n : ℕ, 0 < T / ((n : ℝ) + 2) := by
    intro n
    exact div_pos hT (by positivity)
  have hle : ∀ n : ℕ, T / ((n : ℝ) + 2) ≤ T := by
    intro n
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 2)).2
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
    nlinarith
  have hanti : Antitone (fun n : ℕ => T / ((n : ℝ) + 2)) := by
    intro a b hab
    dsimp
    have hab' : (a : ℝ) ≤ (b : ℝ) := Nat.cast_le.mpr hab
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < (b : ℝ) + 2)
        (by positivity : (0 : ℝ) < (a : ℝ) + 2)).2
    nlinarith [mul_nonneg (le_of_lt hT) (sub_nonneg.mpr hab')]
  have hbase : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hsum : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [(tendsto_atTop.1 hbase b)] with n hn
    linarith
  have hinv : Tendsto (fun n : ℕ => (((n : ℝ) + 2)⁻¹))
      atTop (nhds (0 : ℝ)) := tendsto_inv_atTop_zero.comp hsum
  have hlim : Tendsto (fun n : ℕ => T / ((n : ℝ) + 2))
      atTop (nhds (0 : ℝ)) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_const_nhds.mul hinv)
  exact ⟨hpos, hle, hanti, hlim⟩
