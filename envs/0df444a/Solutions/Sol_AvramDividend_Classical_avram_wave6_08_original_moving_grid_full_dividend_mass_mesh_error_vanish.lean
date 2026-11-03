-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_08_original_moving_grid_full_dividend_mass_mesh_error_vanish
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T08:01:46.124558+00:00
-- url     : https://prove2.me/submissions/682cd01e-c430-4707-99ba-4ee4baec4e78

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_Ioc_rightLimit
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendStrategy_rightLimit_monotone
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0)
    (u : ℕ → ℕ → ℝ≥0) (hu : ∀ n, Monotone (u n))
    (k : ℕ → ℕ) (hbound : ∀ n, u n (k n) ≤ T)
    (mesh : ℕ → ℝ) (hmesh : ∀ n, 0 ≤ mesh n)
    (hmesh0 : Tendsto mesh atTop (𝓝 0)) :
    Tendsto (fun n =>
      (ENNReal.ofReal (q * mesh n) *
        dividendMeasure D ω
          (Ioc (u n 0 : ℝ) (u n (k n) : ℝ))).toReal)
      atTop (𝓝 0) := by
  have hMon : Monotone (fun t : ℝ≥0 => rightLimit D t ω) :=
    avram_wave3_03_dividendStrategy_rightLimit_monotone D hD ω
  let R : ℝ := rightLimit D T ω - rightLimit D 0 ω
  have hRepr (n : ℕ) (a b : ℝ≥0) (hab : a ≤ b) :
      (ENNReal.ofReal (q * mesh n) *
        dividendMeasure D ω (Ioc (a : ℝ) (b : ℝ))).toReal =
      q * mesh n * (rightLimit D b ω - rightLimit D a ω) := by
    rw [dividendMeasure_Ioc_rightLimit D hD ω a b, ENNReal.toReal_mul]
    rw [ENNReal.toReal_ofReal (mul_nonneg hq (hmesh n)),
      ENNReal.toReal_ofReal (sub_nonneg.mpr (hMon hab))]
  have hTerm (n : ℕ) :
      rightLimit D (u n (k n)) ω - rightLimit D (u n 0) ω ≤ R := by
    have h0 := hMon (show (0 : ℝ≥0) ≤ u n 0 from bot_le)
    have hT := hMon (hbound n)
    dsimp [R]
    linarith only [h0, hT]
  have hL (n : ℕ) :
      0 ≤ q * mesh n * (rightLimit D (u n (k n)) ω -
        rightLimit D (u n 0) ω) :=
    mul_nonneg (mul_nonneg hq (hmesh n))
      (sub_nonneg.mpr (hMon ((hu n) (Nat.zero_le (k n)))))
  have hU (n : ℕ) :
      q * mesh n * (rightLimit D (u n (k n)) ω -
        rightLimit D (u n 0) ω) ≤ q * mesh n * R :=
    mul_le_mul_of_nonneg_left (hTerm n) (mul_nonneg hq (hmesh n))
  have hLim : Tendsto (fun n => q * mesh n * R) atTop (𝓝 0) := by
    convert (tendsto_const_nhds.mul hmesh0).mul tendsto_const_nhds using 1 <;> simp
  refine squeeze_zero (g := fun n => q * mesh n * R) ?_ ?_ hLim
  · intro n
    rw [hRepr n (u n 0) (u n (k n)) ((hu n) (Nat.zero_le (k n)))]
    exact hL n
  · intro n
    rw [hRepr n (u n 0) (u n (k n)) ((hu n) (Nat.zero_le (k n)))]
    exact hU n
