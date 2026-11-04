-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_c_generator_discounted_finite_clock_physical_drift_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:12:32.979502+00:00
-- url     : https://prove2.me/submissions/fff346ec-ebb1-495f-accf-45d11983b64a

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_compact_physical_drift_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- The original epsilon-renormalised physical drift is discounted L¹ on a
finite interior observation clock, using only source Lévy and C² bounds. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    {T : Type*} [mT : MeasurableSpace T]
    (μ : Measure T) [IsFiniteMeasure μ]
    (R clock : T → ℝ) (w : ℝ → ℝ) (q : ℝ)
    (hder : Measurable (fun t => deriv w (R t)))
    (hcmeas : Measurable clock) (hcpos : ∀ t, 0 ≤ clock t)
    (hq : 0 ≤ q) (A : Set T) (hA : MeasurableSet A)
    (C u v ε : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hu : 0 < u) (hv : v < C) (hε : 0 < ε)
    (hcap : ∀ t ∈ A, R t ∈ Icc u v) :
    Integrable (A.indicator (fun t : T =>
      Real.exp (-(q * clock t)) *
        ((X.c - (∫ z in Ioo (-1 : ℝ) (-ε), z ∂X.ν)) *
          deriv w (R t)))) μ := by
  classical
  obtain ⟨_, B, hB⟩ :=
    avram_p4_c_generator_compact_physical_drift_bound
      X w C u v ε hw hu hv hε
  let d : T → ℝ := fun t =>
    (X.c - (∫ z in Ioo (-1 : ℝ) (-ε), z ∂X.ν)) * deriv w (R t)
  have hdmeas : Measurable d := measurable_const.mul hder
  have hmasked : Integrable (A.indicator d) μ := by
    apply (integrable_const |B|).mono'
      (hdmeas.indicator hA).aestronglyMeasurable
    filter_upwards [] with t
    by_cases ht : t ∈ A
    · simpa only [Set.indicator_of_mem ht, Real.norm_eq_abs, d] using
        (hB (R t) (hcap t ht)).trans (le_abs_self B)
    · simp [Set.indicator, ht]
  let a : T → ℝ := fun t => Real.exp (-(q * clock t))
  have hameas : Measurable a := by
    dsimp [a]
    fun_prop
  have habound : ∀ t, |a t| ≤ (1 : ℝ) := by
    intro t
    change |Real.exp (-(q * clock t))| ≤ 1
    rw [abs_of_pos (Real.exp_pos _)]
    have hle : -(q * clock t) ≤ 0 :=
      neg_nonpos.mpr (mul_nonneg hq (hcpos t))
    simpa only [Real.exp_zero] using (Real.exp_le_exp.mpr hle)
  have hweighted : Integrable (fun t => a t * (A.indicator d t)) μ := by
    apply Integrable.bdd_mul hmasked hameas.aestronglyMeasurable (c := 1)
    filter_upwards [] with t
    simpa only [Real.norm_eq_abs] using habound t
  have hEq : (A.indicator (fun t : T => a t * d t)) =
      (fun t => a t * (A.indicator d t)) := by
    funext t
    by_cases ht : t ∈ A
    · simp [Set.indicator, ht]
    · simp [Set.indicator, ht]
  change Integrable (A.indicator (fun t : T => a t * d t)) μ
  rw [hEq]
  exact hweighted
