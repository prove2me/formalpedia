-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_08_original_dividend_full_mesh_mass_error_vanish
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T07:55:10.878541+00:00
-- url     : https://prove2.me/submissions/ffa01109-4ca8-4d42-8ee4-7f2b6d2c3bc2

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
    (mesh : ℕ → ℝ) (hmesh : ∀ n, 0 ≤ mesh n)
    (hmesh0 : Tendsto mesh atTop (𝓝 0)) :
    Tendsto (fun n =>
      (ENNReal.ofReal (q * mesh n) *
        dividendMeasure D ω (Ioc (0 : ℝ) (T : ℝ))).toReal)
      atTop (𝓝 0) := by
  have hMon : Monotone (fun t : ℝ≥0 => rightLimit D t ω) :=
    avram_wave3_03_dividendStrategy_rightLimit_monotone D hD ω
  have h0T : (0 : ℝ≥0) ≤ T := by positivity
  have hR : 0 ≤ rightLimit D T ω - rightLimit D 0 ω :=
    sub_nonneg.mpr (hMon h0T)
  have hMass :
      dividendMeasure D ω (Ioc (0 : ℝ) (T : ℝ)) =
        ENNReal.ofReal (rightLimit D T ω - rightLimit D 0 ω) := by
    simpa using dividendMeasure_Ioc_rightLimit D hD ω (0 : ℝ≥0) T
  have hPoint (n : ℕ) :
      (ENNReal.ofReal (q * mesh n) *
        dividendMeasure D ω (Ioc (0 : ℝ) (T : ℝ))).toReal =
      q * mesh n * (rightLimit D T ω - rightLimit D 0 ω) := by
    rw [hMass, ENNReal.toReal_mul]
    rw [ENNReal.toReal_ofReal (mul_nonneg hq (hmesh n)),
      ENNReal.toReal_ofReal hR]
  have hLimit : Tendsto
      (fun n => q * mesh n * (rightLimit D T ω - rightLimit D 0 ω))
      atTop (𝓝 0) := by
    convert (tendsto_const_nhds.mul hmesh0).mul tendsto_const_nhds using 1 <;> simp
  simpa only [hPoint] using hLimit
