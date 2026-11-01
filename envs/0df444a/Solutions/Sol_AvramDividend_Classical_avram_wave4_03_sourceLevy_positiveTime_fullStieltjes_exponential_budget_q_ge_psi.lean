-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_03_sourceLevy_positiveTime_fullStieltjes_exponential_budget_q_ge_psi
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T00:00:16.302188+00:00
-- url     : https://prove2.me/submissions/3f9b879f-3e5d-40e3-a12d-8222bc3ce6be

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_sourceLevy_positiveTime_fullStieltjes_exponential_budget
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
/-- Source Lévy exponential full-Stieltjes expected budget for any discount above ψ(1). -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : X.ψ 1 ≤ q)
    (T : ℝ≥0) (hT : 0 < T) :
    (∫⁻ ω, ∫⁻ s : ℝ,
      if s ∈ Ioc (0 : ℝ) (T : ℝ) then
        ENNReal.ofReal (Real.exp
          (X.X s.toNNReal ω - rightLimit D s.toNNReal ω -
            (s.toNNReal : ℝ) * q))
      else 0 ∂dividendMeasure D ω ∂P) ≤ 1 := by
  classical
  have hpoint (ω : Ω) (s : ℝ) :
      (if s ∈ Ioc (0 : ℝ) (T : ℝ) then
        ENNReal.ofReal (Real.exp
          (X.X s.toNNReal ω - rightLimit D s.toNNReal ω -
            (s.toNNReal : ℝ) * q))
      else 0) ≤
      (if s ∈ Ioc (0 : ℝ) (T : ℝ) then
        ENNReal.ofReal (Real.exp
          (X.X s.toNNReal ω - rightLimit D s.toNNReal ω -
            (s.toNNReal : ℝ) * X.ψ 1))
      else 0) := by
    by_cases hs : s ∈ Ioc (0 : ℝ) (T : ℝ)
    · simp only [if_pos hs]
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      have ht : 0 ≤ (s.toNNReal : ℝ) := NNReal.coe_nonneg _
      have hm := mul_le_mul_of_nonneg_left hq ht
      linarith
    · simp only [if_neg hs, le_refl]
  have hinner (ω : Ω) :
      (∫⁻ s : ℝ, if s ∈ Ioc (0 : ℝ) (T : ℝ) then
        ENNReal.ofReal (Real.exp
          (X.X s.toNNReal ω - rightLimit D s.toNNReal ω -
            (s.toNNReal : ℝ) * q))
      else 0 ∂dividendMeasure D ω) ≤
      (∫⁻ s : ℝ, if s ∈ Ioc (0 : ℝ) (T : ℝ) then
        ENNReal.ofReal (Real.exp
          (X.X s.toNNReal ω - rightLimit D s.toNNReal ω -
            (s.toNNReal : ℝ) * X.ψ 1))
      else 0 ∂dividendMeasure D ω) :=
    lintegral_mono (hpoint ω)
  exact le_trans (lintegral_mono hinner)
    (avram_wave4_03_sourceLevy_positiveTime_fullStieltjes_exponential_budget X D hD T hT)
