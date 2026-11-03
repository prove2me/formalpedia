-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_02_original_BV_uniform_piecewise_negative_mark_envelope_on_predictable_strip
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T23:50:24.886921+00:00
-- url     : https://prove2.me/submissions/a28abae5-aa50-4108-b649-6bb239529320

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_C1_large_negative_mark_discounted_candidate_uniform_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_C1_predictable_small_mark_discounted_L1_by_source_variation
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Original physical left-reserve nonlinear marked kernel has a uniform mark-only BV first-moment/finite-tail envelope on a predictable interior strip. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (q : ℝ) (hq : 0 ≤ q)
    (a b L R : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hL : 0 ≤ L) (hR : 0 ≤ R)
    (hBound : ∀ v : ℝ, v ≤ b → |w v| ≤ R)
    (hLip : ∀ u ∈ Icc (a / 2) b, ∀ v ∈ Icc (a / 2) b,
      |w u - w v| ≤ L * |u - v|)
    (E : Set (ℝ≥0 × Ω))
    (hBand : ∀ p ∈ E, Function.leftLim (fun s : ℝ≥0 =>
      x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc a b)
    (p : ℝ≥0 × Ω) (hp : p ∈ E) (z : ℝ) (hz : z < 0) :
    |Real.exp (-(q * (p.1 : ℝ))) *
      (w (Function.leftLim (fun s : ℝ≥0 =>
        x + X.X s p.2 - rightLimit D s p.2) p.1 + z) -
       w (Function.leftLim (fun s : ℝ≥0 =>
        x + X.X s p.2 - rightLimit D s p.2) p.1))| ≤
      if z ≤ -a / 2 then 2 * R else L * |z| := by
  split_ifs with hCut
  · exact
      avram_wave7_02_original_BV_C1_large_negative_mark_discounted_candidate_uniform_bound
        X x D w q hq a b R ha hab hR hBound
        p.2 p.1 (hBand p hp) z hCut
  · have hzSmall : -a / 2 ≤ z ∧ z ≤ 0 :=
      ⟨le_of_lt (lt_of_not_ge hCut), le_of_lt hz⟩
    exact
      avram_wave7_02_original_BV_C1_predictable_small_mark_discounted_L1_by_source_variation
        X x D w q hq a b L ha hab hL hLip
        p.2 p.1 (hBand p hp) z hzSmall
