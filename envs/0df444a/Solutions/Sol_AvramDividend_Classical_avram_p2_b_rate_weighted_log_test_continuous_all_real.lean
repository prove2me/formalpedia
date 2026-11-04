-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_b_rate_weighted_log_test_continuous_all_real
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:41:47.910303+00:00
-- url     : https://prove2.me/submissions/a12d4a2f-12e7-4037-80bb-15202ab43962

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_negative_test_weighted_log_vanishes_near_one

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology

theorem solution
    (f : ℝ → ℝ) (hf : Continuous f) (a ε : ℝ) (hε : 0 < ε)
    (hflower : ∀ y : ℝ, y < a → f y = 0)
    (hfupper : ∀ y : ℝ, -ε < y → f y = 0) :
    Continuous (fun z : ℝ => f (Real.log z) / (z - 1) ^ 4) := by
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz0 : z = 0
  · subst z
    have hfzero : f 0 = 0 := hfupper 0 (by linarith)
    have hlt : |(0 : ℝ)| ∈ Iio (Real.exp a) := by
      simpa using Real.exp_pos a
    have hev : ∀ᶠ z in nhds (0 : ℝ), |z| < Real.exp a :=
      continuous_abs.continuousAt.tendsto.eventually
        (isOpen_Iio.mem_nhds hlt)
    have heq : (fun z : ℝ => f (Real.log z) / (z - 1) ^ 4) =ᶠ[nhds (0 : ℝ)]
        (fun _ : ℝ => 0) := by
      filter_upwards [hev] with z hz
      by_cases hz' : z = 0
      · subst z
        simp [hfzero]
      · have hpos : 0 < |z| := abs_pos.mpr hz'
        have hlogabs : Real.log |z| < a :=
          (Real.log_lt_iff_lt_exp hpos).mpr hz
        have hlog : Real.log z < a := by
          simpa only [Real.log_abs] using hlogabs
        simp [hflower (Real.log z) hlog]
    exact heq.continuousAt
  by_cases hz1 : z = 1
  · subst z
    have heq :=
      AvramDividend.Classical.avram_p2_b_rate_negative_test_weighted_log_vanishes_near_one
        f ε hε hfupper
    exact heq.continuousAt
  have hnum : ContinuousAt (fun w : ℝ => f (Real.log w)) z :=
    hf.continuousAt.comp (Real.continuousAt_log hz0)
  have hden : ContinuousAt (fun w : ℝ => (w - 1) ^ 4) z :=
    (continuousAt_id.sub continuousAt_const).pow 4
  have hden_ne : (z - 1) ^ 4 ≠ 0 := pow_ne_zero 4 (sub_ne_zero.mpr hz1)
  exact hnum.div hden hden_ne
