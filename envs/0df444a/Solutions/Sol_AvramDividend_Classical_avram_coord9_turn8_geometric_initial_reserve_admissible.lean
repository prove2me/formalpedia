-- Prove2me | solution 1 for AvramDividend.Classical.avram_coord9_turn8_geometric_initial_reserve_admissible
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T00:46:26.055008+00:00
-- url     : https://prove2.me/submissions/0979450d-ec62-4017-97b7-e20edef330e3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_coord9_turn8_random_zero_lump_dividend_strategy
import Theorems.Thm_AvramDividend_Classical_avram_e0_initial_only_dividend_rightlimit
import Theorems.Thm_AvramDividend_Classical_avram_e0_initial_step_admissible_infinite_cap_of_rightLimit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A geometrically marked positive reserve gives an affordable, adapted
    immediate dividend and hence an exact original infinite-cap strategy. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (K : Ω → ℕ) (y : ℕ → ℝ)
    (hy : ∀ k, 0 ≤ y k)
    (hyle : ∀ k, y k ≤ x)
    (hadapt : ∀ t : ℝ≥0, 0 < t →
      Measurable[𝓕 t] (fun ω : Ω => y (K ω))) :
    IsAdmissibleLe X x ⊤
      (fun t ω => if t = 0 then 0 else x - y (K ω)) := by
  let L : Ω → ℝ := fun ω => x - y (K ω)
  have hL_nonneg : ∀ ω, 0 ≤ L ω := by
    intro ω
    exact sub_nonneg.mpr (hyle (K ω))
  have hL_adapt : ∀ t : ℝ≥0, 0 < t → Measurable[𝓕 t] L := by
    intro t ht
    exact measurable_const.sub (hadapt t ht)
  have hstrategy : IsDividendStrategy 𝓕
      (fun t ω => if t = 0 then 0 else L ω) :=
    avram_coord9_turn8_random_zero_lump_dividend_strategy L hL_nonneg hL_adapt
  have hright : ∀ ω (t : ℝ≥0),
      rightLimit (fun s ω => if s = 0 then 0 else L ω) t ω = L ω := by
    intro ω t
    exact avram_e0_initial_only_dividend_rightlimit L ω t
  have hLle : ∀ ω, L ω ≤ x := by
    intro ω
    exact sub_le_self x (hy (K ω))
  change IsAdmissibleLe X x ⊤
    (fun t ω => if t = 0 then 0 else L ω)
  exact avram_e0_initial_step_admissible_infinite_cap_of_rightLimit
    X x L hstrategy hright hLle
