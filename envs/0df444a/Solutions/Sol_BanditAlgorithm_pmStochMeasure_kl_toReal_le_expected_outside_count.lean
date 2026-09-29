-- Prove2me | solution 1 for BanditAlgorithm.pmStochMeasure_kl_toReal_le_expected_outside_count
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-05T19:26:36.0743+00:00
-- url     : https://prove2.me/submissions/15b88fe4-ce7c-40ca-b48c-21d50277cd20

import Theorems.Thm_BanditAlgorithm_pmStochMeasure_kl_le_outside_selection
import Theorems.Thm_BanditAlgorithm_pmStoch_expected_actionSetCount_eq_selection_mass

open MeasureTheory ProbabilityTheory InformationTheory
open scoped BigOperators ENNReal

namespace BanditAlgorithm

theorem _root_.solution
    {k d : ℕ} {𝕊 : Type*} [Fintype 𝕊] [MeasurableSpace 𝕊]
    (G : PartialMonitoringGame k d 𝕊) (π : PMPolicy k 𝕊)
    (u v : Fin d → ℝ) (hu : u ∈ stdSimplex ℝ (Fin d))
    (hv : v ∈ stdSimplex ℝ (Fin d)) (N : Finset (Fin k)) (B : ℝ≥0∞)
    (hB : B ≠ ⊤)
    (hfin : ∀ c, klDiv (pmSignalMeasure G u c) (pmSignalMeasure G v c) ≠ ⊤)
    (heq : ∀ c, c ∈ N → pmSignalMeasure G u c = pmSignalMeasure G v c)
    (hle : ∀ c, c ∉ N → klDiv (pmSignalMeasure G u c)
      (pmSignalMeasure G v c) ≤ B) : ∀ n : ℕ,
    (klDiv (pmStochMeasure G π u hu n)
      (pmStochMeasure G π v hv n)).toReal ≤
      B.toReal *
        ∫ h, ∑ t : Fin n,
          (if (h t).1 ∉ N then (1 : ℝ) else 0)
          ∂pmStochMeasure G π u hu n := by
  classical
  intro n
  let S : Finset (Fin k) := Finset.univ.filter (fun c => c ∉ N)
  let X : ℝ≥0∞ := ∑ t ∈ Finset.range n,
    ∫⁻ h, ∑ c ∈ S, (π.select t h) {c}
      ∂pmStochMeasure G π u hu t
  have hmass (t : ℕ) (h : PMHistory k 𝕊 t) :
      ∑ c ∈ S, (π.select t h) {c} ≤ 1 := by
    calc
      ∑ c ∈ S, (π.select t h) {c} = (π.select t h) (S : Set (Fin k)) := by
        simp
      _ ≤ (π.select t h) Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  have hmeas (t : ℕ) : Measurable (fun h : PMHistory k 𝕊 t =>
      ∑ c ∈ S, (π.select t h) {c}) := by
    apply Finset.measurable_sum
    intro c hc
    exact Kernel.measurable_coe (π.select t) (MeasurableSet.singleton _)
  have hterm_ne (t : ℕ) :
      (∫⁻ h, ∑ c ∈ S, (π.select t h) {c}
        ∂pmStochMeasure G π u hu t) ≠ ⊤ := by
    have hle_one : (∫⁻ h, ∑ c ∈ S, (π.select t h) {c}
        ∂pmStochMeasure G π u hu t) ≤ 1 := by
      calc
        (∫⁻ h, ∑ c ∈ S, (π.select t h) {c}
            ∂pmStochMeasure G π u hu t) ≤
            ∫⁻ _h : PMHistory k 𝕊 t, (1 : ℝ≥0∞)
              ∂pmStochMeasure G π u hu t := lintegral_mono (hmass t)
        _ = 1 := by simp
    exact ne_top_of_le_ne_top (by simp) hle_one
  have hX_ne : X ≠ ⊤ := by
    unfold X
    exact ENNReal.sum_ne_top.mpr fun t ht => hterm_ne t
  have hkl := pmStochMeasure_kl_le_outside_selection
    G π u v hu hv N B hfin heq hle n
  change klDiv (pmStochMeasure G π u hu n)
      (pmStochMeasure G π v hv n) ≤ B * X at hkl
  have hkl_ne : klDiv (pmStochMeasure G π u hu n)
      (pmStochMeasure G π v hv n) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top hB hX_ne) hkl
  have hreal := ENNReal.toReal_mono (ENNReal.mul_ne_top hB hX_ne) hkl
  rw [ENNReal.toReal_mul] at hreal
  have hXreal : X.toReal =
      ∫ h, ∑ t : Fin n, (if (h t).1 ∉ N then (1 : ℝ) else 0)
        ∂pmStochMeasure G π u hu n := by
    rw [show (∫ h, ∑ t : Fin n,
          (if (h t).1 ∉ N then (1 : ℝ) else 0)
          ∂pmStochMeasure G π u hu n) =
        ∫ h, ∑ t : Fin n,
          (if (h t).1 ∈ S then (1 : ℝ) else 0)
          ∂pmStochMeasure G π u hu n by
      apply integral_congr_ae
      filter_upwards [] with h
      apply Finset.sum_congr rfl
      intro t ht
      simp [S]]
    rw [pmStoch_expected_actionSetCount_eq_selection_mass G π u hu S n]
    unfold X
    rw [ENNReal.toReal_sum (fun t ht => hterm_ne t)]
    apply Finset.sum_congr rfl
    intro t ht
    rw [← integral_toReal (hmeas t).aemeasurable]
    · apply integral_congr_ae
      filter_upwards [] with h
      rw [ENNReal.toReal_sum]
      · rfl
      · intro c hc
        exact measure_ne_top _ _
    · filter_upwards [] with h
      exact lt_of_le_of_lt (hmass t h) ENNReal.one_lt_top
  rw [hXreal] at hreal
  exact hreal

end BanditAlgorithm
