-- Prove2me | solution 1 for AvramDividend.Classical.projective_martingale_early_events_fixed_terminal_law
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T23:14:09.332959+00:00
-- url     : https://prove2.me/submissions/9657b10c-d3d3-45c3-b22f-decde13f21ca

import Mathlib.Probability.Process.Filtration
import Theorems.Thm_AvramDividend_Classical_setIntegral_eq_of_ambient_measures_agree_on_subsigma
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (Q : ℝ≥0 → Measure Ω)
    (Z : ℝ≥0 → Ω → ℝ)
    (hQ : ∀ s t : ℝ≥0, s ≤ t →
      ∀ A : Set Ω, @MeasurableSet Ω (𝓕 s) A → Q s A = Q t A)
    (hZ : ∀ s t : ℝ≥0, s ≤ t →
      ∀ A : Set Ω, @MeasurableSet Ω (𝓕 s) A →
        (∫ ω in A, Z s ω ∂Q s) = (∫ ω in A, Z t ω ∂Q t))
    (hadapt : ∀ t : ℝ≥0, StronglyMeasurable[𝓕 t] (Z t))
    (s t T : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T)
    (A : Set Ω) (hA : @MeasurableSet Ω (𝓕 s) A) :
    (∫ ω in A, Z s ω ∂Q T) =
    (∫ ω in A, Z t ω ∂Q T) := by
  have hsT : s ≤ T := le_trans hst htT
  have hAt : @MeasurableSet Ω (𝓕 t) A := (𝓕.mono hst) A hA
  have hsQ : (∫ ω in A, Z s ω ∂Q s) =
      (∫ ω in A, Z s ω ∂Q T) := by
    exact setIntegral_eq_of_ambient_measures_agree_on_subsigma
      (𝓕.le s) (Q s) (Q T)
      (fun B hB => hQ s T hsT B hB) A hA (Z s) (hadapt s)
  have htQ : (∫ ω in A, Z t ω ∂Q t) =
      (∫ ω in A, Z t ω ∂Q T) := by
    exact setIntegral_eq_of_ambient_measures_agree_on_subsigma
      (𝓕.le t) (Q t) (Q T)
      (fun B hB => hQ t T htT B hB) A hAt (Z t) (hadapt t)
  calc
    (∫ ω in A, Z s ω ∂Q T) =
      (∫ ω in A, Z s ω ∂Q s) := hsQ.symm
    _ = (∫ ω in A, Z t ω ∂Q t) := hZ s t hst A hA
    _ = (∫ ω in A, Z t ω ∂Q T) := htQ
