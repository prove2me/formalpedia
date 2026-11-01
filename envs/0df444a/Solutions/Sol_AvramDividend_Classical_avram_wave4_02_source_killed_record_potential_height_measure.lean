-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_02_source_killed_record_potential_height_measure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T11:36:58.700795+00:00
-- url     : https://prove2.me/submissions/f96a72bf-9e95-4c27-a18a-976c7a67c3f6

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_atomless_positive_tail_measure_of_antitone_continuous
import Theorems.Thm_AvramDividend_Classical_avram_wave4_02_source_esscher_record_height_rate_nonneg_continuous
import Theorems.Thm_AvramDividend_Classical_avram_wave4_02_source_esscher_record_height_rate_antitone
import Theorems.Thm_AvramDividend_Classical_avram_wave4_02_source_esscher_record_height_rate_tendsto_zero
import Theorems.Thm_AvramDividend_Classical_avram_wave4_02_source_esscher_killed_potential_interval_representation
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Topology

/-- A true source killed-first-record potential determines an atomless
height measure with finite positive tails and the exact scale ratio.
This is not a construction of the Itô excursion PPP characteristic n. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : (∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν) = ⊤)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (V : ℝ → ℝ)
    (hV : ∀ z : ℝ, 0 < z → V z = Real.exp (-(φ * z)) * W z) :
    ∃ μ : Measure ℝ,
      NullSingletonClass μ ∧
      (∀ x : ℝ, 0 < x → μ (Ici x) ≠ ⊤) ∧
      (∀ x : ℝ, 0 < x →
        μ.real (Ici x) =
          -Real.log ((∫⁻ ω, if twoSidedExitUpTime X 1 ω <
            barrierRuinTime X x ω then
            ENNReal.ofReal
              (Real.exp (-(q * (twoSidedExitUpTime X 1 ω).toReal)))
          else 0 ∂P).toReal) - φ) ∧
      (∀ x a : ℝ, 0 < x → x ≤ a →
        V x / V a =
          Real.exp (-(∫ t in x..a, μ.real (Ici t)))) := by
  let rate : ℝ → ℝ := fun x =>
    -Real.log ((∫⁻ ω, if twoSidedExitUpTime X 1 ω <
      barrierRuinTime X x ω then
      ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X 1 ω).toReal)))
    else 0 ∂P).toReal) - φ
  have hcont : ContinuousOn rate (Ioi (0 : ℝ)) := by
    exact (avram_wave4_02_source_esscher_record_height_rate_nonneg_continuous
      X q hq W hW hvar φ hφ hroot).1
  have hnonneg : ∀ x : ℝ, 0 < x → 0 ≤ rate x := by
    exact (avram_wave4_02_source_esscher_record_height_rate_nonneg_continuous
      X q hq W hW hvar φ hφ hroot).2
  have hanti : AntitoneOn rate (Ioi (0 : ℝ)) := by
    intro a ha b hb hab
    exact avram_wave4_02_source_esscher_record_height_rate_antitone
      X q hq W hW hvar φ hφ hroot a b ha hab
  have hlim : Tendsto rate atTop (nhds (0 : ℝ)) := by
    exact avram_wave4_02_source_esscher_record_height_rate_tendsto_zero
      X q hq W hW hvar φ hφ hroot
  obtain ⟨μ, hnull, hfinite, htail⟩ :=
    atomless_positive_tail_measure_of_antitone_continuous
      rate hcont hanti hnonneg hlim
  refine ⟨μ, hnull, hfinite, htail, ?_⟩
  intro x a hx hxa
  have hsource :
      V x / V a = Real.exp (-(∫ t in x..a, rate t)) := by
    exact avram_wave4_02_source_esscher_killed_potential_interval_representation
      X q hq W hW hvar φ hφ hroot V hV x a hx hxa
  calc
    V x / V a = Real.exp (-(∫ t in x..a, rate t)) := hsource
    _ = Real.exp (-(∫ t in x..a, μ.real (Ici t))) := by
      apply congrArg Real.exp
      apply congrArg (fun z : ℝ => -z)
      apply intervalIntegral.integral_congr
      intro t ht
      have ht' : t ∈ Icc x a := by
        simpa only [uIcc_of_le hxa] using ht
      exact (htail t (lt_of_lt_of_le hx ht'.1)).symm
