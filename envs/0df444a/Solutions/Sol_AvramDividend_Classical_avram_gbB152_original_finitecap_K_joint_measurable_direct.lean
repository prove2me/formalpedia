-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB152_original_finitecap_K_joint_measurable_direct
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T11:39:15.793096+00:00
-- url     : https://prove2.me/submissions/17bcdd5d-cb4a-4dc0-88fc-e439dceb1e3c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB55_original_finitecap_postpayment_gradient_grid_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (hn : 0 < n)
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (δ : ℝ) (hδ : 0 < δ) (j : ℕ) :
    let G : ℕ → ℕ → Ω → ℝ := fun m i ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
      let s : ℝ≥0 := (i : ℝ≥0) * Δ
      let a : ℝ := δ / 2
      let b : ℝ := C.toReal *
        (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
      let Y : ℝ := x + X.X s ω - rightLimit D s ω
      if s < ρ ω then Real.exp (-(q * (s : ℝ))) *
        (if Y ∈ Icc a b then deriv w Y else 1)
      else 0
    let K : ℕ → ℝ → Ω → ℝ := fun m t ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
      let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
      (Finset.range (m + 1)).sum (fun i =>
        if (s i : ℝ) ≤ t ∧ t < ((s i + Δ : ℝ≥0) : ℝ)
        then G m i ω else 0)
    ∀ m, Measurable (fun z : ℝ × Ω => K m z.1 z.2) := by
  intro G K m
  have hg :=
    avram_gbB55_original_finitecap_postpayment_gradient_grid_measurable
      X q hq w C hC hFiniteCap hw_smooth x D hD n hn ρ hρstop δ hδ j
  let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
  let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
  classical
  have hf : ∀ i ∈ Finset.range (m + 1), StronglyMeasurable
      (fun z : ℝ × Ω =>
        if (s i : ℝ) ≤ z.1 ∧ z.1 < ((s i + Δ : ℝ≥0) : ℝ)
        then G m i z.2 else 0) := by
    intro i hi
    have hc : MeasurableSet
        {z : ℝ × Ω |
          (s i : ℝ) ≤ z.1 ∧ z.1 < ((s i + Δ : ℝ≥0) : ℝ)} := by
      measurability
    have hgi : StronglyMeasurable (fun z : ℝ × Ω => G m i z.2) :=
      ((hg m i).stronglyMeasurable).comp_measurable measurable_snd
    exact StronglyMeasurable.ite hc hgi stronglyMeasurable_const
  have hsum := Finset.stronglyMeasurable_sum (Finset.range (m + 1)) hf
  have heq :
      (∑ i ∈ Finset.range (m + 1), (fun z : ℝ × Ω =>
        if (s i : ℝ) ≤ z.1 ∧ z.1 < ((s i + Δ : ℝ≥0) : ℝ)
        then G m i z.2 else 0)) =
      (fun z => ∑ i ∈ Finset.range (m + 1),
        if (s i : ℝ) ≤ z.1 ∧ z.1 < ((s i + Δ : ℝ≥0) : ℝ)
        then G m i z.2 else 0) := by
    funext z
    simp
  have hh : Measurable (fun z : ℝ × Ω =>
      (Finset.range (m + 1)).sum (fun i =>
        if (s i : ℝ) ≤ z.1 ∧ z.1 < ((s i + Δ : ℝ≥0) : ℝ)
        then G m i z.2 else 0)) := by
    rw [← heq]
    exact hsum.measurable
  simpa only [K, Δ, s] using hh
