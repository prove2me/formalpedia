-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger87_original_strict_rightlimit_le_later_dividend
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T10:01:37.051628+00:00
-- url     : https://prove2.me/submissions/52e79a12-6be3-45a4-9f60-ce4c1082aa84

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendStrategy_rightLimit_monotone
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_rightLimit_leftLimit_eq_dividend
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (a b : ℝ≥0) (hab : a < b) :
    rightLimit D a ω ≤ D b ω := by
  have hbpos : 0 < b := lt_of_le_of_lt (zero_le : (0 : ℝ≥0) ≤ a) hab
  haveI : NeBot (𝓝[<] b) := nhdsLT_neBot_of_exists_lt ⟨a, hab⟩
  have hmon := avram_wave3_03_dividendStrategy_rightLimit_monotone D hD ω
  have hlim := avram_wave3_04_rightLimit_leftLimit_eq_dividend D hD ω b hbpos
  have hnear : Ioi a ∈ 𝓝 b := IsOpen.mem_nhds isOpen_Ioi hab
  have hnearL : Ioi a ∈ 𝓝[<] b := nhdsWithin_le_nhds hnear
  have hev : ∀ᶠ t in 𝓝[<] b, rightLimit D a ω ≤ rightLimit D t ω := by
    filter_upwards [hnearL] with t ht
    exact hmon (le_of_lt ht)
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hlim hev
