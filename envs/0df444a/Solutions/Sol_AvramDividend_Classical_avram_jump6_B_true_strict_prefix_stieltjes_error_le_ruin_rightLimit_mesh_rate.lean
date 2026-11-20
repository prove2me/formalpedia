-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_true_strict_prefix_stieltjes_error_le_ruin_rightLimit_mesh_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T20:41:43.660338+00:00
-- url     : https://prove2.me/submissions/87be48e9-5fef-4b99-bc83-0a54e9875cb2

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_Ioc_rightLimit
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendStrategy_rightLimit_monotone
import Theorems.Thm_AvramDividend_Classical_avram_ga_a35_original_dividend_rightLimit_nonnegative
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (t ρ : ℝ≥0) (htρ : t ≤ ρ)
    (q : ℝ) (hq : 0 < q) (n : ℕ) (hn : 0 < n) (j : ℕ) :
    (ENNReal.ofReal (q * ((1 : ℝ) / ((j : ℝ) + 1))) *
        dividendMeasure D ω (Ioc (0 : ℝ) (t : ℝ))).toReal ≤
      q * ((n : ℝ) / ((j : ℝ) + 1)) *
        Real.exp (q * (n : ℝ)) * rightLimit D ρ ω := by
  have hm : Monotone (fun s : ℝ≥0 => rightLimit D s ω) :=
    avram_wave3_03_dividendStrategy_rightLimit_monotone D hD ω
  have h0 : 0 ≤ rightLimit D 0 ω :=
    avram_ga_a35_original_dividend_rightLimit_nonnegative D hD 0 ω
  have hnonneg : 0 ≤ rightLimit D t ω - rightLimit D 0 ω :=
    sub_nonneg.mpr (hm (zero_le : (0 : ℝ≥0) ≤ t))
  have hdelta : rightLimit D t ω - rightLimit D 0 ω ≤
      rightLimit D ρ ω := by
    have hh := hm htρ
    linarith
  have hrho : 0 ≤ rightLimit D ρ ω :=
    avram_ga_a35_original_dividend_rightLimit_nonnegative D hD ρ ω
  have hmass :=
    dividendMeasure_Ioc_rightLimit D hD ω (0 : ℝ≥0) t
  have hmassReal :
      dividendMeasure D ω (Ioc (0 : ℝ) (t : ℝ)) =
        ENNReal.ofReal (rightLimit D t ω - rightLimit D 0 ω) := by
    simpa using hmass
  have hcoeff : 0 ≤ q * ((1 : ℝ) / ((j : ℝ) + 1)) := by positivity
  have hreal :
      (ENNReal.ofReal (q * ((1 : ℝ) / ((j : ℝ) + 1))) *
        dividendMeasure D ω (Ioc (0 : ℝ) (t : ℝ))).toReal =
      (q * ((1 : ℝ) / ((j : ℝ) + 1))) *
        (rightLimit D t ω - rightLimit D 0 ω) := by
    rw [hmassReal, ← ENNReal.ofReal_mul hcoeff]
    rw [ENNReal.toReal_ofReal (mul_nonneg hcoeff hnonneg)]
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hexp : (1 : ℝ) ≤ Real.exp (q * (n : ℝ)) := by
    apply Real.one_le_exp
    positivity
  have hfactor : (1 : ℝ) ≤
      (n : ℝ) * Real.exp (q * (n : ℝ)) := by
    nlinarith [Real.exp_pos (q * (n : ℝ))]
  have hrate :
      q * ((1 : ℝ) / ((j : ℝ) + 1)) ≤
      q * ((n : ℝ) / ((j : ℝ) + 1)) *
        Real.exp (q * (n : ℝ)) := by
    calc
      q * ((1 : ℝ) / ((j : ℝ) + 1)) =
        (q * ((1 : ℝ) / ((j : ℝ) + 1))) * 1 := by ring
      _ ≤ (q * ((1 : ℝ) / ((j : ℝ) + 1))) *
        ((n : ℝ) * Real.exp (q * (n : ℝ))) :=
          mul_le_mul_of_nonneg_left hfactor hcoeff
      _ = q * ((n : ℝ) / ((j : ℝ) + 1)) *
          Real.exp (q * (n : ℝ)) := by ring
  rw [hreal]
  calc
    (q * ((1 : ℝ) / ((j : ℝ) + 1))) *
      (rightLimit D t ω - rightLimit D 0 ω) ≤
      (q * ((1 : ℝ) / ((j : ℝ) + 1))) *
        rightLimit D ρ ω :=
          mul_le_mul_of_nonneg_left hdelta hcoeff
    _ ≤ q * ((n : ℝ) / ((j : ℝ) + 1)) *
      Real.exp (q * (n : ℝ)) * rightLimit D ρ ω :=
        mul_le_mul_of_nonneg_right hrate hrho