-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_bv_original_killed_terminal_one_sided_liminf_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T07:49:06.278124+00:00
-- url     : https://prove2.me/submissions/c291cb7d-273f-48b6-981b-64a35d448df4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_discounted_killed_terminal_left_tendsto_ae

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- The original discounted killed terminal is lower semicontinuous from the
left in the epsilon-eventual sense, even if ruin occurs exactly at the horizon. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (x : ℝ) (w : ℝ → ℝ) (hw : ContinuousOn w (Ici 0)) (q : ℝ)
    (hwnn : ∀ ω (s : ℝ≥0), 0 < s →
      (s : ℝ≥0∞) < ruinTime X x D ω → 0 ≤ w (riskProcess X x D s ω))
    (t : ℝ≥0) (ht : 0 < t) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ s : ℝ≥0 in 𝓝[<] t,
        (if (t : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * (t : ℝ))) * w (riskProcess X x D t ω) else 0) - ε <
        (if (s : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * (s : ℝ))) * w (riskProcess X x D s ω) else 0) := by
  filter_upwards [avram_p3_bv_original_discounted_killed_terminal_left_tendsto_ae
    X D hD x w hw q t ht] with ω hLeft
  intro ε hε
  by_cases hSurv : (t : ℝ≥0∞) < ruinTime X x D ω
  · have hBelow :
        Real.exp (-(q * (t : ℝ))) * w (riskProcess X x D t ω) - ε <
        Real.exp (-(q * (t : ℝ))) * w (riskProcess X x D t ω) :=
      sub_lt_self _ hε
    simpa [hSurv] using (hLeft hSurv).eventually (Ioi_mem_nhds hBelow)
  · have hId : Tendsto (fun s : ℝ≥0 => s) (𝓝[<] t) (𝓝 t) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have hPos : ∀ᶠ s : ℝ≥0 in 𝓝[<] t, (0 : ℝ≥0) < s :=
      hId.eventually (Ioi_mem_nhds ht)
    filter_upwards [hPos] with s hspos
    have hTerminal :
        0 ≤ (if (s : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * (s : ℝ))) * w (riskProcess X x D s ω) else 0) := by
      split_ifs with hEarlier
      · exact mul_nonneg (le_of_lt (Real.exp_pos _)) (hwnn ω s hspos hEarlier)
      · exact le_refl _
    have hSmall : (0 : ℝ) - ε < 0 := by linarith
    simpa [hSurv] using lt_of_lt_of_le hSmall hTerminal
