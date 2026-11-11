-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18_standing_X_integrable_fixedtime
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T20:18:39.588824+00:00
-- url     : https://prove2.me/submissions/b4c2f4bc-6c79-4161-b3df-6dccf3e2baf0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_integrable_at_natural_horizon_of_standing

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The original process is integrable at every deterministic time under
Standing. A natural horizon supplies an L1 terminal state, while the
Laplace and stationary-increment fields bound both positive tails. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) :
    ∀ t : ℝ≥0, Integrable (X.X t) P := by
  letI : IsProbabilityMeasure P := X.isProbability
  intro t
  obtain ⟨n, hn⟩ := exists_nat_ge t
  have hN : Integrable (X.X (n : ℝ≥0)) P :=
    levy_integrable_at_natural_horizon_of_standing X hX n
  have hEt : Integrable (fun ω => Real.exp (X.X t ω)) P := by
    simpa only [one_mul] using (X.laplace t 1 (by norm_num)).1
  have hEb : Integrable
      (fun ω => Real.exp (X.X (n : ℝ≥0) ω - X.X t ω)) P := by
    have hDist := (X.stationaryIncrements t (n : ℝ≥0) hn).comp
      Real.measurable_exp
    have hE : Integrable (fun ω => Real.exp (X.X ((n : ℝ≥0) - t) ω)) P := by
      simpa only [one_mul] using
        (X.laplace ((n : ℝ≥0) - t) 1 (by norm_num)).1
    simpa only [Function.comp_def] using hDist.integrable_iff.mpr hE
  have hDom : Integrable
      (fun ω => ‖X.X (n : ℝ≥0) ω‖ + Real.exp (X.X t ω) +
        Real.exp (X.X (n : ℝ≥0) ω - X.X t ω)) P :=
    (hN.norm.add hEt).add hEb
  have hMeas : Measurable (X.X t) :=
    (X.adapted t).mono (𝓕.le t) le_rfl
  apply hDom.mono' hMeas.aestronglyMeasurable
  filter_upwards [] with ω
  have hPoint (a b : ℝ) :
      |a| ≤ |a + b| + Real.exp a + Real.exp b := by
    by_cases ha : 0 ≤ a
    · rw [abs_of_nonneg ha]
      have he := Real.add_one_le_exp a
      have hn := abs_nonneg (a + b)
      have hp := (Real.exp_pos b).le
      linarith
    · have han : a < 0 := lt_of_not_ge ha
      rw [abs_of_neg han]
      have he := Real.add_one_le_exp b
      have hn := neg_le_abs (a + b)
      have hp := (Real.exp_pos a).le
      linarith
  have hb := hPoint (X.X t ω) (X.X (n : ℝ≥0) ω - X.X t ω)
  have hs : X.X t ω + (X.X (n : ℝ≥0) ω - X.X t ω) =
      X.X (n : ℝ≥0) ω := by ring
  rw [hs] at hb
  simpa only [Real.norm_eq_abs] using hb
