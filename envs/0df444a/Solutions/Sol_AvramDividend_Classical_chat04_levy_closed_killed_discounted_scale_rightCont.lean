-- Prove2me | solution 1 for AvramDividend.Classical.chat04_levy_closed_killed_discounted_scale_rightCont
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T11:00:09.19517+00:00
-- url     : https://prove2.me/submissions/898b8869-6b3e-4631-bec9-a1100cd48394

import Theorems.Thm_AvramDividend_Classical_chat04_rightContinuous_masked_reward_of_zero_boundary
import Theorems.Thm_AvramDividend_Classical_chat04_closed_survival_locally_stable_of_rightCont_positive
import Theorems.Thm_AvramDividend_Classical_chat03_discounted_scale_right_continuous_of_Wzero
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical AvramDividend.Classical MeasureTheory Filter Set Topology
open scoped NNReal

/-- The discounted scale payoff killed at the first negative reserve is
    pathwise right-continuous at every deterministic horizon. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q x : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hzero : W 0 = 0)
    (discount : ℝ≥0 → ℝ) (hdiscount : Continuous discount)
    (ω : Ω) (t : ℝ≥0) :
    ContinuousWithinAt
      (fun u : ℝ≥0 =>
        if (∀ s : ℝ≥0, s ≤ u → 0 ≤ x + X.X s ω)
        then discount u * W (x + X.X u ω)
        else 0)
      (Ici t) t := by
  classical
  let f : ℝ≥0 → ℝ := fun u => x + X.X u ω
  let g : ℝ≥0 → ℝ := fun u => discount u * W (f u)
  have hf : ContinuousWithinAt f (Ici t) t := by
    change Tendsto (fun u : ℝ≥0 => x + X.X u ω)
      (𝓝[Ici t] t) (𝓝 (x + X.X t ω))
    exact (continuousAt_const.add continuousAt_id).tendsto.comp
      (X.rightCont ω t).tendsto
  have hg : ContinuousWithinAt g (Ici t) t := by
    exact chat03_discounted_scale_right_continuous_of_Wzero
      X q x W hW hzero discount hdiscount ω t
  have hmask : ContinuousWithinAt
      (fun u => if (∀ s : ℝ≥0, s ≤ u → 0 ≤ f s) then g u else 0)
      (Ici t) t := by
    refine chat04_rightContinuous_masked_reward_of_zero_boundary
      g (fun u : ℝ≥0 => ∀ s : ℝ≥0, s ≤ u → 0 ≤ f s)
      t hg ?_ ?_
    · intro hsurv hnz
      have hft : 0 ≤ f t := hsurv t le_rfl
      have hpos : 0 < f t := by
        rcases lt_or_eq_of_le hft with hlt | heq
        · exact hlt
        · have hgt : g t = 0 := by
            dsimp [g]
            rw [show f t = 0 from heq.symm, hzero, mul_zero]
          exact False.elim (hnz hgt)
      exact chat04_closed_survival_locally_stable_of_rightCont_positive
        f t hf hpos hsurv
    · intro hnot
      have hge : ∀ᶠ u in 𝓝[Ici t] t, t ≤ u := self_mem_nhdsWithin
      filter_upwards [hge] with u htu hu
      apply hnot
      intro s hst
      exact hu s (hst.trans htu)
  simpa only [f, g] using hmask
