-- Prove2me | solution 1 for BanditAlgorithm.bandit_stopped_bretagnolle_huber
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-30T19:37:47.279637+00:00
-- url     : https://prove2.me/submissions/f9eab387-1039-47b6-b467-e5487a157e26

import Theorems.Thm_BanditAlgorithm_bandit_stopped_klDiv_le_expected_information
import Theorems.Thm_BanditAlgorithm_bretagnolle_huber_inequality

open MeasureTheory ProbabilityTheory InformationTheory ENNReal
open BanditAlgorithm

theorem solution
    {k : ℕ} (ν ν' : StochasticBandit k) (π : BanditPolicy k)
    (τ : (ℕ → Fin k × ℝ) → ℕ∞) (hτ : IsBanditStoppingTime τ)
    (hfinite : ∫⁻ ω, (τ ω : ℝ≥0∞) ∂banditTrajMeasure ν π < ⊤)
    (A : Set (ℕ → Fin k × ℝ)) (hA : Measurable[hτ.measurableSpace] A)
    (hinfo : (∑ i, (∫⁻ ω, ∑' t : ℕ,
          if (t : ℕ∞) < τ ω ∧ (ω t).1 = i then (1 : ℝ≥0∞) else 0
        ∂banditTrajMeasure ν π) * klDiv (ν.P i) (ν'.P i)) ≠ ⊤) :
    (2 : ℝ)⁻¹ * Real.exp
        (-(∑ i, (∫⁻ ω, ∑' t : ℕ,
            if (t : ℕ∞) < τ ω ∧ (ω t).1 = i then (1 : ℝ≥0∞) else 0
          ∂banditTrajMeasure ν π) * klDiv (ν.P i) (ν'.P i)).toReal) ≤
      (banditTrajMeasure ν π).real Aᶜ +
        (banditTrajMeasure ν' π).real A := by
  let I : ℝ≥0∞ :=
    ∑ i, (∫⁻ ω, ∑' t : ℕ,
        if (t : ℕ∞) < τ ω ∧ (ω t).1 = i then (1 : ℝ≥0∞) else 0
      ∂banditTrajMeasure ν π) * klDiv (ν.P i) (ν'.P i)
  let Pτ : @Measure (ℕ → Fin k × ℝ) hτ.measurableSpace :=
    (banditTrajMeasure ν π).trim hτ.measurableSpace_le
  let Qτ : @Measure (ℕ → Fin k × ℝ) hτ.measurableSpace :=
    (banditTrajMeasure ν' π).trim hτ.measurableSpace_le
  let D : ℝ≥0∞ := @klDiv (ℕ → Fin k × ℝ) hτ.measurableSpace Pτ Qτ
  have hDI : D ≤ I := by
    exact BanditAlgorithm.bandit_stopped_klDiv_le_expected_information
      ν ν' π τ hτ hfinite
  have hDtop : D ≠ ⊤ := ne_top_of_le_ne_top hinfo hDI
  have htoReal : D.toReal ≤ I.toReal := ENNReal.toReal_mono hinfo hDI
  letI : @IsProbabilityMeasure (ℕ → Fin k × ℝ) hτ.measurableSpace Pτ :=
    ⟨by
      rw [trim_measurableSet_eq hτ.measurableSpace_le
        (@MeasurableSet.univ _ hτ.measurableSpace)]
      exact measure_univ⟩
  letI : @IsProbabilityMeasure (ℕ → Fin k × ℝ) hτ.measurableSpace Qτ :=
    ⟨by
      rw [trim_measurableSet_eq hτ.measurableSpace_le
        (@MeasurableSet.univ _ hτ.measurableSpace)]
      exact measure_univ⟩
  have hAset : @MeasurableSet (ℕ → Fin k × ℝ) hτ.measurableSpace A :=
    (@measurableSet_setOf _ hτ.measurableSpace _).mpr hA
  have hAc : @MeasurableSet (ℕ → Fin k × ℝ) hτ.measurableSpace Aᶜ :=
    hAset.compl
  have hBH :
      (2 : ℝ)⁻¹ * Real.exp (-D.toReal) ≤ Pτ.real Aᶜ + Qτ.real A := by
    simpa [D] using
      (BanditAlgorithm.bretagnolle_huber_inequality Pτ Qτ hAc hDtop)
  calc
    (2 : ℝ)⁻¹ * Real.exp (-I.toReal) ≤
        (2 : ℝ)⁻¹ * Real.exp (-D.toReal) := by
      gcongr
    _ ≤ Pτ.real Aᶜ + Qτ.real A := hBH
    _ = (banditTrajMeasure ν π).real Aᶜ +
        (banditTrajMeasure ν' π).real A := by
      simp only [Pτ, Qτ, Measure.real]
      rw [trim_measurableSet_eq hτ.measurableSpace_le hAc,
        trim_measurableSet_eq hτ.measurableSpace_le hAset]
