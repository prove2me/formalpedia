-- Prove2me | solution 1 for AvramDividend.Classical.avram_b76_original_true_ruinclock_contact_jump_discounted_generator_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T12:56:52.631975+00:00
-- url     : https://prove2.me/submissions/ab139160-8757-497d-95dd-d0181a9b1189

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_b69_original_true_spatial_clock_ruin_clipped
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_actual_inclusive_ruin_jump_chronological_discounted_generator_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The genuine original ruin-clipped spatial stopping-clock negative contact mark keeps the full discounted generator upper bound. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth :
      (¬ X.BoundedVariation →
        ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation →
        ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (ρ : Ω → ℝ≥0)
    (hρbound : ∀ ω, ρ ω ≤ (n : ℝ≥0))
    (hρclip : ∀ ω, ρ ω ≤
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (κ : ℕ → Ω → ℝ≥0)
    (hκexact : ∀ k ω, κ k ω =
      (min (ρ ω : ℝ≥0∞)
        (twoSidedExitUpTime X ((k : ℝ) + 1) ω)).toNNReal)
    (k : ℕ) (ω : Ω) (ht : 0 < κ k ω)
    (q : ℝ) (hq : 0 ≤ q)
    (u v ζ : ℝ) :
    let t : ℝ≥0 := κ k ω
    let Y : ℝ := Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
    let J : ℝ :=
      X.X t ω - Function.leftLim (fun s : ℝ≥0 => X.X s ω) t
    let W : ℝ :=
      if (t : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X t ω - rightLimit D t ω
      else riskProcess X x D t ω
    let cash : ℝ :=
      if (t : ℝ≥0∞) < ruinTime X x D ω then
        rightLimit D t ω - D t ω else 0
    ∀ (hJneg : J < 0) (hBand : Y ∈ Icc (u + ζ) v),
    Real.exp (-(q * (t : ℝ))) *
      ((w W -
          w (Function.leftLim (fun s : ℝ≥0 =>
            riskProcess X x D s ω) t)) + cash) ≤
    Real.exp (-(q * (t : ℝ))) *
      ((if -1 < J then J * deriv w Y else 0) +
        SpectrallyNegativeLevy.generatorIntegrand w Y J) := by
  intro t Y J W cash hJneg hBand
  have hClock :=
    avram_b69_original_true_spatial_clock_ruin_clipped
      X x D n ρ hρclip κ hκexact k ω
  have htT : κ k ω ≤ (n : ℝ≥0) :=
    (hClock.1.trans (hρbound ω))
  exact avram_wave5_03_actual_inclusive_ruin_jump_chronological_discounted_generator_bound
    X w C hC hw_cont hw_smooth hw_grad x hxc D hD
    ω (n : ℝ≥0) (κ k ω) ht htT hClock.2
    q hq u v ζ hJneg hBand
