-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p2_all_original_levy_jump_times_countable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T16:38:02.201081+00:00
-- url     : https://prove2.me/submissions/ff56de3d-284e-42a2-80a4-d76001fe394f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_nonpositive

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) :
    Set.Countable {t : ℝ≥0 |
      0 < t ∧ X.X t ω ≠ Function.leftLim
        (fun s : ℝ≥0 => X.X s ω) t} := by
  let S (r : ℚ) : Set ℝ≥0 :=
    {t | 0 < t ∧ X.X t ω < (r : ℝ) ∧
      (r : ℝ) < Function.leftLim (fun s : ℝ≥0 => X.X s ω) t}
  have hcount (r : ℚ) : (S r).Countable := by
    apply (countable_setOfPred_isolated_left_within (s := S r)).mono
    intro t ht
    refine ⟨ht, ?_⟩
    have htpos : 0 < t := ht.1
    obtain ⟨l, hl⟩ := X.leftLim ω t htpos
    letI : (𝓝[<] t).NeBot :=
      nhdsLT_neBot_of_exists_lt ⟨0, htpos⟩
    have hleft : Function.leftLim (fun u : ℝ≥0 => X.X u ω) t = l :=
      leftLim_eq_of_tendsto hl
    have hr : (r : ℝ) < l := by
      simpa only [hleft] using ht.2.2
    have hevent : ∀ᶠ u in 𝓝[<] t, (r : ℝ) < X.X u ω := by
      exact hl.eventually (isOpen_Ioi.mem_nhds hr)
    have hsmall : 𝓝[S r ∩ Iio t] t ≤ 𝓝[<] t :=
      nhdsWithin_mono t inter_subset_right
    have hevent' : ∀ᶠ u in 𝓝[S r ∩ Iio t] t,
        (r : ℝ) < X.X u ω := hevent.filter_mono hsmall
    by_contra hbot
    letI : (𝓝[S r ∩ Iio t] t).NeBot := ⟨hbot⟩
    have hmem : ∀ᶠ u in 𝓝[S r ∩ Iio t] t, u ∈ S r :=
      (eventually_mem_nhdsWithin).mono (fun _ hu => hu.1)
    obtain ⟨u, hu, hur⟩ := (hmem.and hevent').exists
    exact (lt_asymm hu.2.1 hur)
  have hcount_all : (⋃ r : ℚ, S r).Countable :=
    Set.countable_iUnion hcount
  apply hcount_all.mono
  intro t ht
  have hle : X.X t ω ≤
      Function.leftLim (fun s : ℝ≥0 => X.X s ω) t :=
    sub_nonpos.mp (avram_wave4_04a_actual_levy_jumpmark_nonpositive
      X ω t ht.1)
  have hlt : X.X t ω <
      Function.leftLim (fun s : ℝ≥0 => X.X s ω) t :=
    lt_of_le_of_ne hle ht.2
  obtain ⟨r, hr₁, hr₂⟩ := exists_rat_btwn hlt
  exact Set.mem_iUnion.mpr ⟨r, ⟨ht.1, hr₁, hr₂⟩⟩
