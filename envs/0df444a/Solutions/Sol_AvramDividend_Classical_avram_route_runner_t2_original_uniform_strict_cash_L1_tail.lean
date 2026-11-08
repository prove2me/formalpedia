-- Prove2me | solution 1 for AvramDividend.Classical.avram_route_runner_t2_original_uniform_strict_cash_L1_tail
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T13:25:59.284686+00:00
-- url     : https://prove2.me/submissions/d361e84b-d12e-4c88-a732-497f36968fdc

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_cash_cofinal_L1_error_tendsto_zero
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_uniform_strict_mesh_cofinal_at_horizon
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ) (hT : 0 < T) :
    Tendsto (fun n : ℕ => ∫ ω : Ω,
      |(∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω)).toReal -
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
          Iio (T - T / ((n : ℝ) + 2)),
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω)).toReal| ∂P)
      atTop (𝓝 0) := by
  let u : ℕ → ℝ := fun n => T - T / ((n : ℝ) + 2)
  have hlim : Tendsto u atTop (𝓝 T) :=
    (avram_p3_grid4_original_uniform_strict_mesh_cofinal_at_horizon T hT).2
  have hmono : Monotone u := by
    intro a b hab
    have hab' : (a : ℝ) + 2 ≤ (b : ℝ) + 2 := by
      have hcast : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
      linarith
    have hfrac : T / ((b : ℝ) + 2) ≤ T / ((a : ℝ) + 2) :=
      div_le_div_of_nonneg_left (le_of_lt hT) (by positivity) hab'
    exact sub_le_sub_left hfrac T
  have hu : ∀ n, 0 ≤ u n := by
    intro n
    change 0 ≤ T - T / ((n : ℝ) + 2)
    apply sub_nonneg.mpr
    have hden : 1 ≤ (n : ℝ) + 2 := by
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
      linarith
    apply (div_le_iff₀ (by positivity)).2
    calc
      T = T * 1 := by ring
      _ ≤ T * ((n : ℝ) + 2) :=
        mul_le_mul_of_nonneg_left hden (le_of_lt hT)
  have hbelow : ∀ n, u n ≤ T := by
    intro n
    change T - T / ((n : ℝ) + 2) ≤ T
    exact sub_le_self T (div_nonneg (le_of_lt hT) (by positivity))
  have hcover : ∀ s : ℝ, s < T → ∃ n, s < u n := by
    intro s hs
    exact (hlim.eventually (Ioi_mem_nhds hs)).exists
  exact avram_p3_bv_original_strict_cash_cofinal_L1_error_tendsto_zero
    X x C D hD q hq ⟨T, le_of_lt hT⟩ u hmono hu hbelow hcover
