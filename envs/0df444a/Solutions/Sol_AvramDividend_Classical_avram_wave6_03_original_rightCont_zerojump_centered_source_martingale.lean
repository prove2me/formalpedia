-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_03_original_rightCont_zerojump_centered_source_martingale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T23:40:26.105652+00:00
-- url     : https://prove2.me/submissions/cb60dcd6-7d2e-47a8-a2ca-8e2b307cdc0c

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_gaussian_deterministic_increment_condExp_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The original source path with zero jump measure has a genuinely centred
martingale in its own right-continuous filtration, for all sigma including zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0) :
    Martingale (fun t ω => X.X t ω - (t : ℝ) * X.c) 𝓕.rightCont P := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let M : ℝ≥0 → Ω → ℝ := fun t ω => X.X t ω - (t : ℝ) * X.c
  change Martingale M 𝓕.rightCont P
  constructor
  · intro t
    exact (((X.adapted t).mono (𝓕.le_rightCont t) le_rfl).sub_const
      ((t : ℝ) * X.c)).stronglyMeasurable
  · intro s t hst
    let Z : Ω → ℝ := fun ω =>
      X.X t ω - X.X s ω - ((t - s) : ℝ) * X.c
    have hZpair :=
      avram_wave6_03_original_rightCont_gaussian_deterministic_increment_condExp_zero
        X hν s t hst
    have hZI : Integrable Z P := hZpair.1
    have hZCE : P[Z | 𝓕.rightCont s] =ᵐ[P]
        (fun _ => (0 : ℝ)) := hZpair.2
    have hM0 :=
      (avram_wave6_03_original_rightCont_gaussian_deterministic_increment_condExp_zero
        X hν 0 s (show (0 : ℝ≥0) ≤ s from zero_le)).1
    have hMsI : Integrable (M s) P := by
      simpa [M, X.X_zero] using hM0
    have hMsStrong : StronglyMeasurable[𝓕.rightCont s] (M s) :=
      (((X.adapted s).mono (𝓕.le_rightCont s) le_rfl).sub_const
        ((s : ℝ) * X.c)).stronglyMeasurable
    have hMsCE : P[M s | 𝓕.rightCont s] = M s :=
      condExp_of_stronglyMeasurable ((𝓕.rightCont).le s)
        hMsStrong hMsI
    have hDecomp : (fun ω => M t ω) =
        (fun ω => M s ω + Z ω) := by
      funext ω
      dsimp [M, Z]
      ring
    have hSumCE :
        P[(fun ω => M s ω + Z ω) | 𝓕.rightCont s] =ᵐ[P]
          (M s) := by
      filter_upwards [condExp_add hMsI hZI (𝓕.rightCont s), hZCE]
        with ω hAdd hZero
      change (P[M s + Z | 𝓕.rightCont s]) ω = M s ω
      rw [hAdd, hMsCE]
      change M s ω + (P[Z | 𝓕.rightCont s]) ω = M s ω
      rw [hZero, add_zero]
    change P[(fun ω => M t ω) | 𝓕.rightCont s] =ᵐ[P] (M s)
    rw [hDecomp]
    exact hSumCE
