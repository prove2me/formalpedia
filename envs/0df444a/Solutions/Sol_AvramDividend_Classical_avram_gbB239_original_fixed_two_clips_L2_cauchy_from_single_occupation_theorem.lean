-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB239_original_fixed_two_clips_L2_cauchy_from_single_occupation_theorem
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T09:51:14.547615+00:00
-- url     : https://prove2.me/submissions/980a0530-dfc5-4060-a5fc-8a33e03de192
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB100_original_gaussian_fixed_level_occupation_null
import Theorems.Thm_AvramDividend_Classical_avram_gbB238_fixed_clipped_physical_mesh_two_level_null_occupation_L2_cauchy
import Theorems.Thm_AvramDividend_Classical_avram_gbB80_original_zerojump_postpayment_ae_countable_discontinuities
import Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_postpayment_reserve_joint_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original fixed two-level mesh Cauchy conditional on exact original Gaussian B100. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (n : ℕ) (hn : 0 < n) (q : ℝ) (hq : 0 ≤ q)
    (w : ℝ → ℝ) (a b : ℝ) (ρ : Ω → ℝ≥0)
    (hρ : Measurable ρ)
    (hDeriv : ∀ y ∈ Set.Ioo a b, ContinuousAt (deriv w) y)
    (hClosed : ContinuousOn (deriv w) (Set.Icc a b)) :
    let Y : ℝ≥0 → Ω → ℝ := fun s ω =>
      x + X.X s ω - rightLimit D s ω
    let K : ℕ → ℝ → Ω → ℝ := fun m t ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
      (Finset.range (m + 1)).sum (fun i =>
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        if (s : ℝ) ≤ t ∧ t < ((s + Δ : ℝ≥0) : ℝ)
        then if (s : ℝ) < (ρ ω : ℝ) then
          Real.exp (-(q * (s : ℝ))) *
            (if Y (Real.toNNReal (s : ℝ)) ω ∈ Set.Icc a b
              then deriv w (Y (Real.toNNReal (s : ℝ)) ω) else 1)
        else 0 else 0)
    Tendsto (fun mp : ℕ × ℕ =>
      ∫ t in Set.Ioo (0 : ℝ) (n : ℝ),
        (∫ ω, (K mp.1 t ω - K mp.2 t ω)^2 ∂P) ∂volume)
      atTop (𝓝 (0 : ℝ)) := by
  intro Y K
  letI : IsProbabilityMeasure P := X.isProbability
  have hY : Measurable (fun z : ℝ≥0 × Ω => Y z.1 z.2) := by
    simpa only [Y] using
      (avram_wave8_20_original_postpayment_reserve_joint_measurable
        X x D hD)
  have hCount :
      ∀ᵐ ω ∂P, Set.Countable {s : ℝ≥0 |
        ¬ ContinuousAt (fun u : ℝ≥0 => Y u ω) s} := by
    simpa only [Y] using
      (avram_gbB80_original_zerojump_postpayment_ae_countable_discontinuities
        X hν D hD x)
  have hOcc (z : ℝ) :
      ∀ᵐ ω ∂P,
        volume {t : ℝ |
          0 < t ∧ t < (n : ℝ) ∧
          Y (Real.toNNReal t) ω = z} = 0 := by
    have hh :=
      avram_gbB100_original_gaussian_fixed_level_occupation_null
        X hBV hν x z D hD n (fun _ => (n : ℝ≥0))
    filter_upwards [hh] with ω hw
    simpa [Y, and_assoc] using hw
  have hh :=
    avram_gbB238_fixed_clipped_physical_mesh_two_level_null_occupation_L2_cauchy
      P Y hY hCount n hn q hq w a b ρ hρ
      (hOcc a) (hOcc b) hDeriv hClosed
  simpa only [Y, K] using hh
