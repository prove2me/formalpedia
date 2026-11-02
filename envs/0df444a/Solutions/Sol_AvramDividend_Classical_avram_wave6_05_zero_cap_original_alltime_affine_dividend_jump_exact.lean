-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_05_zero_cap_original_alltime_affine_dividend_jump_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T20:03:40.756201+00:00
-- url     : https://prove2.me/submissions/b50d8140-1c5e-437a-afa8-9ea70e872a07

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- At literal zero cap, every permitted actual original dividend atom is
exactly the affine cap-linear value drop, including time zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (w V : ℝ → ℝ)
    (hVzero : ∀ y : ℝ,
      V y = if y ≤ 0 then w y else w 0 + y)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (0 : ℝ≥0∞) D)
    (ω : Ω) (t : ℝ≥0)
    (hPre : t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) :
    rightLimit D t ω - D t ω =
      V (riskProcess X x D t ω) -
        V (riskProcess X x D t ω -
          (rightLimit D t ω - D t ω)) := by
  have hAdmissible : IsAdmissible X x D := hD.1
  have hStrategy : IsDividendStrategy 𝓕 D := hAdmissible.1
  let U : ℝ := riskProcess X x D t ω
  let δ : ℝ := rightLimit D t ω - D t ω
  have hPay : 0 ≤ δ :=
    sub_nonneg.mpr (dividendStrategy_le_rightLimit D hStrategy ω t)
  have hSolv : δ ≤ U := hAdmissible.2 ω t hPre
  have hU : 0 ≤ U := le_trans hPay hSolv
  have hPost : 0 ≤ U - δ := by
    linarith only [hSolv]
  have hAffine : ∀ y : ℝ, 0 ≤ y → V y = w 0 + y := by
    intro y hy
    rw [hVzero y]
    split_ifs with hz
    · have heq : y = 0 := le_antisymm hz hy
      subst y
      ring
    · rfl
  have hFirst := hAffine U hU
  have hSecond := hAffine (U - δ) hPost
  change δ = V U - V (U - δ)
  rw [hFirst, hSecond]
  ring
