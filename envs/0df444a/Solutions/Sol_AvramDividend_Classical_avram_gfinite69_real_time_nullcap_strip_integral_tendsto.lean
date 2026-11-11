-- Prove2me | solution 1 for AvramDividend.Classical.avram_gfinite69_real_time_nullcap_strip_integral_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T00:26:39.663206+00:00
-- url     : https://prove2.me/submissions/34110ff5-d2cc-42aa-9a70-b2a9f6785432

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section

theorem solution
    (n : ℕ) (ρ c : ℝ) (U : ℝ → ℝ) (hU : Measurable U)
    (b : ℕ → ℝ) (hbmono : Monotone b)
    (hb : Tendsto b atTop (𝓝 c))
    (hCapNull : volume {t : ℝ |
      0 < t ∧ t < (n : ℝ) ∧ t < ρ ∧ c ≤ U t} = 0) :
    Tendsto (fun j : ℕ =>
      ∫ t in Ioo (0 : ℝ) (n : ℝ),
        if t < ρ ∧ b j < U t then (1 : ℝ) else 0 ∂volume)
      atTop (𝓝 (0 : ℝ)) := by
  classical
  let μ : Measure ℝ := volume.restrict (Ioo (0 : ℝ) (n : ℝ))
  let F : ℕ → ℝ → ℝ := fun j t =>
    if t < ρ ∧ b j < U t then (1 : ℝ) else 0
  have hFMeas (j : ℕ) : AEStronglyMeasurable (F j) μ := by
    have hSet : MeasurableSet {t : ℝ | t < ρ ∧ b j < U t} :=
      (measurableSet_lt measurable_id measurable_const).inter
        (measurableSet_lt measurable_const hU)
    exact (Measurable.ite hSet measurable_const measurable_const).aestronglyMeasurable
  have hFinite : volume (Ioo (0 : ℝ) (n : ℝ)) ≠ ⊤ := by simp
  have hInt : Integrable (fun _ : ℝ => (1 : ℝ)) μ :=
    integrableOn_const hFinite
  have hDom : ∀ j : ℕ, ∀ᵐ t ∂μ, ‖F j t‖ ≤ (1 : ℝ) := by
    intro j
    apply Filter.Eventually.of_forall
    intro t
    by_cases ht : t < ρ ∧ b j < U t <;> simp [F, ht]
  have hBadMeas : MeasurableSet {t : ℝ | t < ρ ∧ c ≤ U t} :=
    (measurableSet_lt measurable_id measurable_const).inter
      (measurableSet_le measurable_const hU)
  have hBad : μ {t : ℝ | t < ρ ∧ c ≤ U t} = 0 := by
    change volume.restrict (Ioo (0 : ℝ) (n : ℝ))
      {t : ℝ | t < ρ ∧ c ≤ U t} = 0
    rw [Measure.restrict_apply hBadMeas]
    have hEq : (Ioo (0 : ℝ) (n : ℝ) ∩
        {t : ℝ | t < ρ ∧ c ≤ U t}) =
        {t : ℝ | 0 < t ∧ t < (n : ℝ) ∧ t < ρ ∧ c ≤ U t} := by
      ext t
      simp only [Set.mem_inter_iff, Set.mem_Ioo, Set.mem_setOf_eq]
      tauto
    rw [Set.inter_comm, hEq]
    exact hCapNull
  have hGood : ∀ᵐ t ∂μ, ¬(t < ρ ∧ c ≤ U t) := by
    rw [ae_iff]
    simpa using hBad
  have hPoint : ∀ᵐ t ∂μ,
      Tendsto (fun j : ℕ => F j t) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [hGood] with t ht
    by_cases htr : t < ρ
    · have huc : U t < c := lt_of_not_ge (fun hge => ht ⟨htr, hge⟩)
      have hEv : ∀ᶠ j in atTop, U t < b j := hb.eventually_const_lt huc
      have hEq : (fun j : ℕ => F j t) =ᶠ[atTop]
          (fun _ => (0 : ℝ)) := by
        filter_upwards [hEv] with j hj
        simp [F, htr, not_lt.mpr (le_of_lt hj)]
      exact tendsto_const_nhds.congr' hEq.symm
    · simpa [F, htr] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  have hDCT := MeasureTheory.tendsto_integral_of_dominated_convergence
    (fun _ : ℝ => (1 : ℝ)) hFMeas hInt hDom hPoint
  simpa [F, μ] using hDCT
