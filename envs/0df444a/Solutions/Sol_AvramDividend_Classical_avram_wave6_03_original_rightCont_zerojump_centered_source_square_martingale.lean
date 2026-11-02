-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_03_original_rightCont_zerojump_centered_source_square_martingale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T00:15:10.685557+00:00
-- url     : https://prove2.me/submissions/e1d8fcb8-ce79-49fb-a4e5-6712d762d38c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_gaussian_deterministic_increment_condExp_variance
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_gaussian_past_cross_increment_condExp_zero
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_gaussian_deterministic_quadratic_residual_condExp_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The squared genuine centred source path minus sigma-squared time
is a true martingale in the original right-continuous filtration. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0) :
    Martingale (fun t ω =>
      (X.X t ω - (t : ℝ) * X.c) ^ 2 - (t : ℝ) * X.σ ^ 2)
      𝓕.rightCont P := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let M : ℝ≥0 → Ω → ℝ := fun u ω => X.X u ω - (u : ℝ) * X.c
  let Q : ℝ≥0 → Ω → ℝ := fun u ω => (M u ω) ^ 2 - (u : ℝ) * X.σ ^ 2
  change Martingale Q 𝓕.rightCont P
  constructor
  · intro u
    have hM : Measurable[𝓕.rightCont u] (M u) :=
      ((X.adapted u).mono (𝓕.le_rightCont u) le_rfl).sub_const
        ((u : ℝ) * X.c)
    have hMSquare : Measurable[𝓕.rightCont u] (fun ω => (M u ω) ^ 2) := by
      convert hM.mul hM using 1
      funext ω
      simp only [Pi.mul_apply, pow_two]
    exact (hMSquare.sub_const ((u : ℝ) * X.σ ^ 2)).stronglyMeasurable
  · intro s t hst
    let Y : Ω → ℝ := fun ω =>
      X.X t ω - X.X s ω - ((t - s) : ℝ) * X.c
    let C : Ω → ℝ := fun ω => M s ω * Y ω
    let R : Ω → ℝ := fun ω => Y ω ^ 2 - ((t - s) : ℝ) * X.σ ^ 2
    have hCPair :=
      avram_wave6_03_original_rightCont_gaussian_past_cross_increment_condExp_zero
        X hν s t hst
    have hCI : Integrable C P := hCPair.1
    have hCCE : P[C | 𝓕.rightCont s] =ᵐ[P] (fun _ => (0 : ℝ)) :=
      hCPair.2
    have hRPair :=
      avram_wave6_03_original_rightCont_gaussian_deterministic_quadratic_residual_condExp_zero
        X hν s t hst
    have hRI : Integrable R P := hRPair.1
    have hRCE : P[R | 𝓕.rightCont s] =ᵐ[P] (fun _ => (0 : ℝ)) :=
      hRPair.2
    have hMsSquareI : Integrable (fun ω => (M s ω) ^ 2) P := by
      have hI :=
        (avram_wave6_03_original_rightCont_gaussian_deterministic_increment_condExp_variance
          X hν 0 s (show (0 : ℝ≥0) ≤ s from zero_le)).1
      simpa [M, X.X_zero] using hI
    have hQsI : Integrable (Q s) P := by
      change Integrable ((fun ω => (M s ω) ^ 2) -
        (fun _ : Ω => (s : ℝ) * X.σ ^ 2)) P
      exact hMsSquareI.sub (integrable_const _)
    have hMsMeas : Measurable[𝓕.rightCont s] (M s) :=
      ((X.adapted s).mono (𝓕.le_rightCont s) le_rfl).sub_const
        ((s : ℝ) * X.c)
    have hMsSquare : Measurable[𝓕.rightCont s] (fun ω => (M s ω) ^ 2) := by
      convert hMsMeas.mul hMsMeas using 1
      funext ω
      simp only [Pi.mul_apply, pow_two]
    have hQsStrong : StronglyMeasurable[𝓕.rightCont s] (Q s) :=
      (hMsSquare.sub_const ((s : ℝ) * X.σ ^ 2)).stronglyMeasurable
    have hQsCE : P[Q s | 𝓕.rightCont s] = Q s :=
      condExp_of_stronglyMeasurable ((𝓕.rightCont).le s) hQsStrong hQsI
    have hQCI : Integrable (Q s + C) P := hQsI.add hCI
    have hQCCI : Integrable ((Q s + C) + C) P := hQCI.add hCI
    have hQC :
        P[Q s + C | 𝓕.rightCont s] =ᵐ[P] Q s := by
      filter_upwards [condExp_add hQsI hCI (𝓕.rightCont s), hCCE]
        with ω ha hc
      change (P[Q s + C | 𝓕.rightCont s]) ω = Q s ω
      rw [ha, hQsCE]
      change Q s ω + (P[C | 𝓕.rightCont s]) ω = Q s ω
      rw [hc, add_zero]
    have hQCC :
        P[(Q s + C) + C | 𝓕.rightCont s] =ᵐ[P] Q s := by
      filter_upwards [condExp_add hQCI hCI (𝓕.rightCont s), hQC, hCCE]
        with ω ha hq hc
      change (P[(Q s + C) + C | 𝓕.rightCont s]) ω = Q s ω
      rw [ha]
      change (P[Q s + C | 𝓕.rightCont s]) ω +
        (P[C | 𝓕.rightCont s]) ω = Q s ω
      rw [hq, hc, add_zero]
    have hQCCR :
        P[((Q s + C) + C) + R | 𝓕.rightCont s] =ᵐ[P] Q s := by
      filter_upwards [condExp_add hQCCI hRI (𝓕.rightCont s), hQCC, hRCE]
        with ω ha hq hr
      change (P[((Q s + C) + C) + R | 𝓕.rightCont s]) ω = Q s ω
      rw [ha]
      change (P[(Q s + C) + C | 𝓕.rightCont s]) ω +
        (P[R | 𝓕.rightCont s]) ω = Q s ω
      rw [hq, hr, add_zero]
    have hDecomp : (fun ω => Q t ω) = ((Q s + C) + C) + R := by
      funext ω
      dsimp [Q, M, C, R, Y]
      ring
    change P[(fun ω => Q t ω) | 𝓕.rightCont s] =ᵐ[P] Q s
    rw [hDecomp]
    exact hQCCR
