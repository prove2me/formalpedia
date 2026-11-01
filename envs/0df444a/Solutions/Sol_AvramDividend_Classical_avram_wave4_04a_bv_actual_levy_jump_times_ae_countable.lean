-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04a_bv_actual_levy_jump_times_ae_countable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T09:57:03.271992+00:00
-- url     : https://prove2.me/submissions/27fdf045-915c-424f-b1f9-d10813ed5cc2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_residual_ae_monotone_all_times

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P,
      Set.Countable {t : ℝ≥0 |
        0 < t ∧ X.X t ω ≠ Function.leftLim
          (fun s : ℝ≥0 => X.X s ω) t} := by
  filter_upwards [bv_actual_levy_residual_ae_monotone_all_times X hBV] with ω hmono
  let Y : ℝ≥0 → ℝ := fun t => (t : ℝ) * X.drift - X.X t ω
  have hmonoY : Monotone Y := hmono
  have hc : Set.Countable {t : ℝ≥0 | ¬ContinuousAt Y t} :=
    hmonoY.countable_not_continuousAt
  apply hc.mono
  intro t ht
  obtain ⟨htpos, hne⟩ := ht
  change ¬ContinuousAt Y t
  intro hYcont
  have hlin : ContinuousAt (fun u : ℝ≥0 => (u : ℝ) * X.drift) t :=
    (NNReal.continuous_coe.mul_const X.drift).continuousAt
  have hXcont : ContinuousAt (fun u : ℝ≥0 => X.X u ω) t := by
    have heq : (fun u : ℝ≥0 => (u : ℝ) * X.drift - Y u) =
        (fun u : ℝ≥0 => X.X u ω) := by
      funext u
      dsimp [Y]
      ring
    have hsub : ContinuousAt (fun u : ℝ≥0 =>
        (u : ℝ) * X.drift - Y u) t := hlin.sub hYcont
    simpa only [heq] using hsub
  obtain ⟨l, hl⟩ := X.leftLim ω t htpos
  letI : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, htpos⟩
  have hvalue : Tendsto (fun s : ℝ≥0 => X.X s ω)
      (𝓝[<] t) (𝓝 (X.X t ω)) :=
    hXcont.tendsto.mono_left nhdsWithin_le_nhds
  have heq : l = X.X t ω := tendsto_nhds_unique hl hvalue
  have hleft : Function.leftLim (fun s : ℝ≥0 => X.X s ω) t = l :=
    leftLim_eq_of_tendsto hl
  exact hne (by rw [hleft, heq])
