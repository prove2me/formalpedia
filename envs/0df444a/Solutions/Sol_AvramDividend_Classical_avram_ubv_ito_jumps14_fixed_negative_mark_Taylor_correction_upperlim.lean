-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_ito_jumps14_fixed_negative_mark_Taylor_correction_upperlim
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T16:32:50.891316+00:00
-- url     : https://prove2.me/submissions/c611de44-5ce6-4873-9de5-bfa2a6a55dde

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_ito_jumps13_zero_extension_upper_semicontinuous_everywhere

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
noncomputable section

/-! Upper semicontinuity of the actual negative-mark Taylor correction, including exact zero contact. -/
theorem solution
    (w : ℝ → ℝ) (hw0 : 0 ≤ w 0)
    (hwcont : ContinuousOn w (Ici 0))
    (hwneg : ∀ y : ℝ, y < 0 → w y = 0)
    (y z : ℝ) (hy : 0 < y) (hz : z < 0)
    (hwy : ContinuousAt w y)
    (hwderiv : ContinuousAt (deriv w) y)
    (u : ℕ → ℝ) (hu : Tendsto u atTop (nhds y)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      w (u n + z) - w (u n) -
        (if -1 < z then z * deriv w (u n) else 0) ≤
      w (y + z) - w y -
        (if -1 < z then z * deriv w y else 0) + ε := by
  intro ε hε
  have hεtwo : 0 < ε / 2 := by linarith
  obtain ⟨δ, hδ, hbound⟩ :=
    avram_ubv_ito_jumps13_zero_extension_upper_semicontinuous_everywhere
      w hw0 hwcont hwneg (y + z) (ε / 2) hεtwo
  have hshift : Tendsto (fun n : ℕ => u n + z) atTop (nhds (y + z)) :=
    hu.add tendsto_const_nhds
  have hpost : ∀ᶠ n : ℕ in atTop,
      u n + z ∈ Metric.ball (y + z) δ :=
    hshift.eventually (Metric.ball_mem_nhds (y + z) hδ)
  let g : ℝ → ℝ := fun v => w v +
    (if -1 < z then z * deriv w v else 0)
  have hg : ContinuousAt g y := by
    by_cases hz' : -1 < z
    · have hsum : ContinuousAt
          (fun v : ℝ => w v + z * deriv w v) y := by
        convert hwy.add (continuousAt_const.mul hwderiv) using 1
        funext v
        rfl
      simpa only [g, if_pos hz'] using hsum
    · simpa [g, hz'] using hwy
  have hcent : Tendsto (fun n : ℕ => g (u n)) atTop (nhds (g y)) :=
    hg.tendsto.comp hu
  have hcenter : ∀ᶠ n : ℕ in atTop,
      g (u n) ∈ Metric.ball (g y) (ε / 2) :=
    hcent.eventually (Metric.ball_mem_nhds (g y) hεtwo)
  filter_upwards [hpost, hcenter] with n hnpost hncenter
  have hupper : w (u n + z) ≤ w (y + z) + ε / 2 :=
    hbound (u n + z) (by
      simpa [Metric.mem_ball, Real.dist_eq] using hnpost)
  have hdiff : |g (u n) - g y| < ε / 2 := by
    simpa [Metric.mem_ball, Real.dist_eq] using hncenter
  have hlow := (abs_lt.mp hdiff).1
  dsimp [g] at hlow
  linarith
