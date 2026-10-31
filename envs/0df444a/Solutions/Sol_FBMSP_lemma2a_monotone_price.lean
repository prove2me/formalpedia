-- Prove2me | solution 1 for FBMSP.lemma2a_monotone_price
-- status  : ACCEPTED   (prove)
-- author  : @mikeh
-- created : 2026-10-30T12:12:10.396057+00:00
-- url     : https://prove2.me/submissions/302bfb39-efb4-49a0-af4f-f1c7ec321130

import Theorems.Thm_FBMSP_singlePrice_attains
import Theorems.Thm_FBMSP_mhr_revenue_tp2

open MeasureTheory FBMSP

theorem solution (η : MeasureTheory.Measure ℝ)
    (hnoise : ValidNoise η) (hmhr : HasMHR η) :
    MonotoneOn (singlePrice η) (Set.Ici (0 : ℝ)) := by
  letI : IsProbabilityMeasure η := hnoise.1
  intro x hx y hy hxy
  obtain ⟨hxLeast, _⟩ := singlePrice_attains η hnoise x hx
  obtain ⟨hyLeast, _⟩ := singlePrice_attains η hnoise y hy
  by_contra hbad
  have hrev : singlePrice η y < singlePrice η x := lt_of_not_ge hbad
  have hweak : postedRevenue η x (singlePrice η y) ≤
      postedRevenue η x (singlePrice η x) :=
    hxLeast.1.2 _ hyLeast.1.1
  have hstrict : postedRevenue η x (singlePrice η y) <
      postedRevenue η x (singlePrice η x) := by
    apply lt_of_le_of_ne hweak
    intro heq
    have hyAtX : IsOptimalPrice η x (singlePrice η y) := by
      refine ⟨hyLeast.1.1, ?_⟩
      intro q hq
      rw [heq]
      exact hxLeast.1.2 q hq
    exact (not_le_of_gt hrev) (hxLeast.2 _ hyAtX)
  have hnonneg : 0 ≤ postedRevenue η x (singlePrice η y) :=
    mul_nonneg hyLeast.1.1 ENNReal.toReal_nonneg
  have hpos : 0 < postedRevenue η x (singlePrice η x) :=
    lt_of_le_of_lt hnonneg hstrict
  have hcol : postedRevenue η x (singlePrice η x) ≤
      postedRevenue η y (singlePrice η x) := by
    unfold postedRevenue survival
    apply mul_le_mul_of_nonneg_left _ hxLeast.1.1
    apply ENNReal.toReal_mono (measure_ne_top η _)
    exact measure_mono (Set.Ici_subset_Ici.mpr
      (sub_le_sub_left hxy (singlePrice η x)))
  have hpos' : 0 < postedRevenue η y (singlePrice η x) :=
    lt_of_lt_of_le hpos hcol
  have hmax' : postedRevenue η y (singlePrice η x) ≤
      postedRevenue η y (singlePrice η y) :=
    hyLeast.1.2 _ hxLeast.1.1
  have hprod₁ :
      postedRevenue η x (singlePrice η y) * postedRevenue η y (singlePrice η x) <
      postedRevenue η x (singlePrice η x) * postedRevenue η y (singlePrice η x) :=
    mul_lt_mul_of_pos_right hstrict hpos'
  have hprod₂ :
      postedRevenue η x (singlePrice η x) * postedRevenue η y (singlePrice η x) ≤
      postedRevenue η x (singlePrice η x) * postedRevenue η y (singlePrice η y) :=
    mul_le_mul_of_nonneg_left hmax' (le_of_lt hpos)
  have htp := mhr_revenue_tp2 η hnoise hmhr x y
    (singlePrice η y) (singlePrice η x) hxy hyLeast.1.1 (le_of_lt hrev)
  exact (not_lt_of_ge htp) (lt_of_lt_of_le hprod₁ hprod₂)
