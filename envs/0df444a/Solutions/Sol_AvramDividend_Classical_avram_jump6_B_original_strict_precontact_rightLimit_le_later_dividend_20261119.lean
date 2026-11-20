-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_original_strict_precontact_rightLimit_le_later_dividend_20261119
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T19:30:58.48076+00:00
-- url     : https://prove2.me/submissions/d8744649-67dc-42cc-9045-7555d8a125fd

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys119_original_dividend_rightLimit_eq_strict_rightLim
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_realTime_monotone
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (hDstrat : IsDividendStrategy 𝓕 D)
    (ω : Ω) (a ρ : ℝ≥0) (h : a < ρ) :
    rightLimit D a ω ≤ D ρ ω := by
  have hmonoReal :
      Monotone (fun t : ℝ => D t.toNNReal ω) :=
    dividendStrategy_realTime_monotone D hDstrat ω
  have hmono : Monotone (fun t : ℝ≥0 => D t ω) := by
    intro s t hst
    have hh : (s : ℝ) ≤ (t : ℝ) := by exact_mod_cast hst
    simpa using hmonoReal hh
  rw [avram_bvb_phys119_original_dividend_rightLimit_eq_strict_rightLim
    X x C D hD ω a]
  exact hmono.rightLim_le h

