-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_02a_actual_source_jump_rational_separation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T13:43:53.279118+00:00
-- url     : https://prove2.me/submissions/f2032c69-7af2-42f6-9e7e-bb540f7ef516

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_nonpositive

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (t : ℝ≥0)
    (ht : 0 < t)
    (hj : X.X t ω - Function.leftLim (fun u : ℝ≥0 => X.X u ω) t ≠ 0) :
    ∃ (a : ℚ) (s b : ℝ≥0), s < t ∧ t < b ∧
      (∀ u ∈ Ioo s t, (a : ℝ) < X.X u ω) ∧
      (∀ u ∈ Ico t b, X.X u ω < (a : ℝ)) := by
  have hle : X.X t ω ≤ Function.leftLim (fun u : ℝ≥0 => X.X u ω) t :=
    sub_nonpos.mp (avram_wave4_04a_actual_levy_jumpmark_nonpositive X ω t ht)
  have hne : X.X t ω ≠ Function.leftLim (fun u : ℝ≥0 => X.X u ω) t := by
    intro h
    apply hj
    rw [h, sub_self]
  have hlt : X.X t ω < Function.leftLim (fun u : ℝ≥0 => X.X u ω) t :=
    lt_of_le_of_ne hle hne
  obtain ⟨a, ha, hb⟩ := exists_rat_btwn hlt
  obtain ⟨l, hl⟩ := X.leftLim ω t ht
  letI : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, ht⟩
  have hleft : Function.leftLim (fun u : ℝ≥0 => X.X u ω) t = l :=
    leftLim_eq_of_tendsto hl
  have ha_left : (a : ℝ) < l := by simpa only [hleft] using hb
  have hEvL : ∀ᶠ u in 𝓝[<] t, (a : ℝ) < X.X u ω :=
    hl.eventually (isOpen_Ioi.mem_nhds ha_left)
  obtain ⟨s, hs, hL⟩ :=
    (mem_nhdsLT_iff_exists_mem_Ico_Ioo_subset ht).mp hEvL
  have hEvR : ∀ᶠ u in 𝓝[≥] t, X.X u ω < (a : ℝ) :=
    (X.rightCont ω t).eventually (isOpen_Iio.mem_nhds ha)
  obtain ⟨b, hb', hR⟩ := mem_nhdsGE_iff_exists_Ico_subset.mp hEvR
  exact ⟨a, s, b, hs.2, hb', hL, hR⟩
