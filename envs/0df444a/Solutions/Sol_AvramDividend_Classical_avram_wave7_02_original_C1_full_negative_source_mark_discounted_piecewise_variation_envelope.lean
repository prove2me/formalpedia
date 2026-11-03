-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_02_original_C1_full_negative_source_mark_discounted_piecewise_variation_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T16:45:34.913719+00:00
-- url     : https://prove2.me/submissions/26c40bac-bda9-4f23-b988-7ccf91a8d753

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_C1_predictable_small_mark_discounted_L1_by_source_variation
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_C1_large_negative_mark_discounted_candidate_uniform_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal Classical
open AvramDividend.Classical
noncomputable section

/-- Every original controlled negative source mark obeys the same integrable
piecewise C1 first-variation/finite-tail envelope, including ruin overshoots. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (q : ℝ) (hq : 0 ≤ q)
    (a b L R : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hL : 0 ≤ L) (hR : 0 ≤ R)
    (hLip : ∀ u ∈ Icc (a / 2) b, ∀ v ∈ Icc (a / 2) b,
      |w u - w v| ≤ L * |u - v|)
    (hWbound : ∀ v : ℝ, v ≤ b → |w v| ≤ R)
    (ω : Ω) (t : ℝ≥0)
    (hBand : Function.leftLim (fun s : ℝ≥0 =>
      x + X.X s ω - rightLimit D s ω) t ∈ Icc a b)
    (z : ℝ) (hz : z < 0) :
    |Real.exp (-(q * (t : ℝ))) *
      (w (Function.leftLim (fun s : ℝ≥0 =>
        x + X.X s ω - rightLimit D s ω) t + z) -
      w (Function.leftLim (fun s : ℝ≥0 =>
        x + X.X s ω - rightLimit D s ω) t))| ≤
      if z ≤ -a / 2 then 2 * R else L * (-z) := by
  split_ifs with hLarge
  · exact avram_wave7_02_original_BV_C1_large_negative_mark_discounted_candidate_uniform_bound
      X x D w q hq a b R ha hab hR hWbound ω t hBand z hLarge
  · have hSmall : -a / 2 ≤ z ∧ z ≤ 0 :=
      ⟨le_of_lt (lt_of_not_ge hLarge), le_of_lt hz⟩
    have hBound :=
      avram_wave7_02_original_BV_C1_predictable_small_mark_discounted_L1_by_source_variation
        X x D w q hq a b L ha hab hL hLip ω t hBand z hSmall
    simpa only [abs_of_neg hz] using hBound
