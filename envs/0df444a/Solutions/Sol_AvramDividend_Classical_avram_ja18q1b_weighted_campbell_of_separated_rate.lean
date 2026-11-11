-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18q1b_weighted_campbell_of_separated_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T01:22:57.479514+00:00
-- url     : https://prove2.me/submissions/d3c8bde3-4edb-48c1-83c2-70d3e3918c7f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_public_mark_marginal_tonelli

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0)
    (hRate : ∀ B : Set ℝ, MeasurableSet B → B ⊆ Iic (-1 : ℝ) →
      (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 t ×ˢ B) ∂P) =
        (t : ℝ≥0∞) * X.ν B) :
    (∫⁻ ω, ∫⁻ p in (Ioc (0 : ℝ≥0) t ×ˢ Iic (-1 : ℝ)),
      ENNReal.ofReal |p.2| ∂
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) ∂P) =
      (t : ℝ≥0∞) *
      (∫⁻ z in Iic (-1 : ℝ), ENNReal.ofReal |z| ∂X.ν) := by
  let S : Set ℝ := Iic (-1 : ℝ)
  let E : Set (ℝ≥0 × ℝ) := Ioc (0 : ℝ≥0) t ×ˢ S
  let N : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  let g : ℝ → ℝ≥0∞ := fun z =>
    if z ∈ S then ENNReal.ofReal |z| else 0
  have hS : MeasurableSet S := measurableSet_Iic
  have hE : MeasurableSet E := measurableSet_Ioc.prod hS
  have hg : Measurable g := by
    exact Measurable.ite hS
      (ENNReal.measurable_ofReal.comp measurable_abs) measurable_const
  obtain ⟨ρ, hρ, hWeighted⟩ :=
    avram_p2_a_zero_rate_original_public_mark_marginal_tonelli X t g hg
  have hMeasures : ρ.restrict S = ((t : ℝ≥0∞) • X.ν).restrict S := by
    apply Measure.ext
    intro B hB
    have hBS : MeasurableSet (B ∩ S) := hB.inter hS
    have hSub : B ∩ S ⊆ Iic (-1 : ℝ) := by
      intro z hz
      exact hz.2
    calc
      (ρ.restrict S) B = ρ (B ∩ S) := Measure.restrict_apply hB
      _ = (∫⁻ ω, N ω (Ioc 0 t ×ˢ (B ∩ S)) ∂P) := hρ _ hBS
      _ = (t : ℝ≥0∞) * X.ν (B ∩ S) := hRate _ hBS hSub
      _ = (((t : ℝ≥0∞) • X.ν).restrict S) B := by
        rw [Measure.restrict_apply hB, Measure.smul_apply]
        simp only [smul_eq_mul]
  have hInner : ∀ ω : Ω,
      (∫⁻ p in E, ENNReal.ofReal |p.2| ∂N ω) =
      (∫⁻ p, (if p.1 ∈ Ioc (0 : ℝ≥0) t then g p.2 else 0) ∂N ω) := by
    intro ω
    rw [← lintegral_indicator hE]
    apply lintegral_congr
    intro p
    by_cases ht : p.1 ∈ Ioc (0 : ℝ≥0) t <;>
      by_cases hz : p.2 ∈ S <;>
      simp [E, g, Set.indicator, ht, hz]
  have hRestrict : (∫⁻ z, g z ∂ρ) =
      (∫⁻ z in S, ENNReal.ofReal |z| ∂ρ) := by
    simpa [g, Set.indicator] using
      (lintegral_indicator (μ := ρ) hS
        (fun z : ℝ => ENNReal.ofReal |z|))
  calc
    (∫⁻ ω, ∫⁻ p in E, ENNReal.ofReal |p.2| ∂N ω ∂P) =
        (∫⁻ ω, ∫⁻ p,
          (if p.1 ∈ Ioc (0 : ℝ≥0) t then g p.2 else 0) ∂N ω ∂P) := by
          exact lintegral_congr hInner
    _ = ∫⁻ z, g z ∂ρ := hWeighted.symm
    _ = ∫⁻ z in S, ENNReal.ofReal |z| ∂ρ := hRestrict
    _ = ∫⁻ z in S, ENNReal.ofReal |z| ∂((t : ℝ≥0∞) • X.ν) := by
      exact congrArg
        (fun μ : Measure ℝ => ∫⁻ z, ENNReal.ofReal |z| ∂μ) hMeasures
    _ = (t : ℝ≥0∞) * (∫⁻ z in S, ENNReal.ofReal |z| ∂X.ν) := by
      simp only [Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul]
