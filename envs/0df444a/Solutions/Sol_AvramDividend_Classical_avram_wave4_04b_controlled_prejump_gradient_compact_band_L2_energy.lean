-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04b_controlled_prejump_gradient_compact_band_L2_energy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T20:10:19.010199+00:00
-- url     : https://prove2.me/submissions/f367e287-519f-4483-9a66-e07c3152a6b7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_compact_gradient_energy_of_measurable_process

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- The analytic compact-gradient lemma applied to the original controlled predictable path. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (a b u v : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo a b))
    (hau : a < u) (huv : u ≤ v) (hvb : v < b)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let H : ℝ≥0 × Ω → ℝ := fun p =>
      if Y p ∈ Icc u v then deriv w (Y p) else 0
    Measurable[𝓕.rightCont.predictable] H ∧
      (∫⁻ p : ℝ≥0 × Ω, ENNReal.ofReal ((H p) ^ 2) ∂μ) < ⊤ := by
  dsimp only
  have hp : IsStronglyPredictable 𝓕.rightCont
      (fun t ω => Function.leftLim (fun s : ℝ≥0 =>
        x + X.X s ω - rightLimit D s ω) t) :=
    avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable X x D hD
  change StronglyMeasurable[𝓕.rightCont.predictable]
    (fun p : ℝ≥0 × Ω => Function.leftLim (fun s : ℝ≥0 =>
      x + X.X s p.2 - rightLimit D s p.2) p.1) at hp
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  have hY : Measurable (fun p : ℝ≥0 × Ω =>
      Function.leftLim (fun s : ℝ≥0 =>
        x + X.X s p.2 - rightLimit D s p.2) p.1) := hp.measurable
  exact avram_wave4_04b_compact_gradient_energy_of_measurable_process
    _ hY w a b u v hw hau huv hvb μ hμ
