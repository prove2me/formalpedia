-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_s3_interval_i_original_postpayment_prejump_left_mesh_converges
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T18:56:11.772198+00:00
-- url     : https://prove2.me/submissions/c9e6a068-83b7-45af-86a4-ef7b51b9a4ec

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_prejump_upper
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_leftLim_leftContinuous_of_exists_leftLimits
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Pathwise convergence of the actual original controlled left-limit reserve
along an arbitrary deterministic mesh approaching a time from below. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (t : ℝ≥0)
    (s : ℕ → ℝ≥0) (hsle : ∀ n, s n ≤ t)
    (hst : Tendsto s atTop (𝓝 t)) :
    Tendsto
      (fun n => Function.leftLim
        (fun u : ℝ≥0 => x + X.X u ω - rightLimit D u ω) (s n))
      atTop
      (𝓝 (Function.leftLim
        (fun u : ℝ≥0 => x + X.X u ω - rightLimit D u ω) t)) := by
  let f : ℝ≥0 → ℝ := fun u => x + X.X u ω - rightLimit D u ω
  have hleft : ∀ u : ℝ≥0, 0 < u →
      ∃ l : ℝ, Tendsto f (𝓝[<] u) (𝓝 l) := by
    intro u hu
    obtain ⟨l, hl, _⟩ :=
      avram_wave3_04_postPaymentReserve_prejump_upper X x D hD ω u hu
    exact ⟨l, hl⟩
  have hc : ContinuousWithinAt (Function.leftLim f) (Iic t) t :=
    avram_wave3_04_leftLim_leftContinuous_of_exists_leftLimits f hleft t
  have hsWithin : Tendsto s atTop (𝓝[Iic t] t) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨hst, Filter.Eventually.of_forall (fun n => hsle n)⟩
  have hComposition :
      Tendsto ((Function.leftLim f) ∘ s) atTop
        (𝓝 (Function.leftLim f t)) := hc.tendsto.comp hsWithin
  change Tendsto (fun n => Function.leftLim f (s n)) atTop
    (𝓝 (Function.leftLim f t)) at hComposition
  exact hComposition
