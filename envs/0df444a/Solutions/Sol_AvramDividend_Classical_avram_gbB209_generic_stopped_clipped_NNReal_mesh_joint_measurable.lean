-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB209_generic_stopped_clipped_NNReal_mesh_joint_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T07:15:20.0457+00:00
-- url     : https://prove2.me/submissions/1278c78d-0d08-41a7-846e-e0af4c749eb7

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
noncomputable section

/-- Joint measurable physical-time grid coefficients. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (Y : ℝ≥0 → Ω → ℝ)
    (hY : Measurable (fun z : ℝ≥0 × Ω => Y z.1 z.2))
    (ρ : Ω → ℝ≥0) (hρ : Measurable ρ)
    (g : ℝ → ℝ) (hg : Measurable g)
    (q : ℝ) (n : ℕ) :
    let F : ℝ≥0 → Ω → ℝ := fun s ω =>
      if s < ρ ω then Real.exp (-(q * (s : ℝ))) * g (Y s ω) else 0
    let K : ℕ → ℝ → Ω → ℝ := fun m t ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
      (Finset.range (m + 1)).sum (fun i =>
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        if (s : ℝ) ≤ t ∧ t < ((s + Δ : ℝ≥0) : ℝ)
        then F s ω else 0)
    let H : ℝ → Ω → ℝ := fun t ω =>
      if Real.toNNReal t < ρ ω then
        Real.exp (-(q * t)) * g (Y (Real.toNNReal t) ω)
      else 0
    (∀ m, Measurable (fun z : ℝ × Ω => K m z.1 z.2)) ∧
    Measurable (fun z : ℝ × Ω => H z.1 z.2) := by
  intro F K H
  have hF : Measurable (fun z : ℝ≥0 × Ω => F z.1 z.2) := by
    have hρz : Measurable (fun z : ℝ≥0 × Ω => ρ z.2) :=
      hρ.comp measurable_snd
    have hset : MeasurableSet {z : ℝ≥0 × Ω | z.1 < ρ z.2} :=
      measurableSet_lt measurable_fst hρz
    have hval : Measurable (fun z : ℝ≥0 × Ω =>
        Real.exp (-(q * (z.1 : ℝ))) * g (Y z.1 z.2)) :=
      (Real.continuous_exp.measurable.comp
        ((measurable_const.mul (NNReal.continuous_coe.measurable.comp measurable_fst)).neg)).mul
        (hg.comp hY)
    simpa only [F] using (hval.ite hset measurable_const)
  have hH : Measurable (fun z : ℝ × Ω => H z.1 z.2) := by
    have hρz : Measurable (fun z : ℝ × Ω => ρ z.2) :=
      hρ.comp measurable_snd
    have ht : Measurable (fun z : ℝ × Ω => Real.toNNReal z.1) :=
      continuous_real_toNNReal.measurable.comp measurable_fst
    have hset : MeasurableSet {z : ℝ × Ω |
        Real.toNNReal z.1 < ρ z.2} := measurableSet_lt ht hρz
    have hval : Measurable (fun z : ℝ × Ω =>
        Real.exp (-(q * z.1)) * g (Y (Real.toNNReal z.1) z.2)) := by
      have hy := hY.comp (ht.prodMk measurable_snd)
      exact (by fun_prop : Measurable (fun z : ℝ × Ω =>
        Real.exp (-(q * z.1)))).mul (hg.comp hy)
    simpa only [H] using (hval.ite hset measurable_const)
  refine ⟨?_, hH⟩
  intro m
  let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
  let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
  have hf : ∀ i ∈ Finset.range (m + 1), StronglyMeasurable
      (fun z : ℝ × Ω =>
        if (s i : ℝ) ≤ z.1 ∧ z.1 < ((s i + Δ : ℝ≥0) : ℝ)
        then F (s i) z.2 else 0) := by
    intro i hi
    have hc : MeasurableSet {z : ℝ × Ω |
      (s i : ℝ) ≤ z.1 ∧ z.1 < ((s i + Δ : ℝ≥0) : ℝ)} := by
      measurability
    have hgi : StronglyMeasurable (fun z : ℝ × Ω => F (s i) z.2) :=
      ((hF.comp (measurable_const.prodMk measurable_snd)).stronglyMeasurable)
    exact StronglyMeasurable.ite hc hgi stronglyMeasurable_const
  have hsum := Finset.stronglyMeasurable_sum (Finset.range (m + 1)) hf
  have heq :
      (∑ i ∈ Finset.range (m + 1), (fun z : ℝ × Ω =>
        if (s i : ℝ) ≤ z.1 ∧ z.1 < ((s i + Δ : ℝ≥0) : ℝ)
        then F (s i) z.2 else 0)) =
      (fun z => ∑ i ∈ Finset.range (m + 1),
        if (s i : ℝ) ≤ z.1 ∧ z.1 < ((s i + Δ : ℝ≥0) : ℝ)
        then F (s i) z.2 else 0) := by
    funext z
    simp
  rw [heq] at hsum
  simpa only [K, Δ, s] using hsum.measurable

