-- Prove2me | solution 1 for AvramDividend.Classical.avram_gb67_original_finitecap_predictable_H_filtered_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T13:00:51.870759+00:00
-- url     : https://prove2.me/submissions/46cd39ad-b745-4f2b-8dd2-b0d263020d45

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gb68_finitecap_compact_hessian_cutoff_measurable
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightLimit_adapted_rightCont
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section
/-- Hessian grid coefficients are predictable in the original filtration. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτmeas : Measurable (fun ω => (τ ω : ℝ)))
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (σ : ℕ → Ω → ℝ≥0)
    (hσstop : ∀ k, IsStoppingTime 𝓕.rightCont
      (fun ω => (σ k ω : WithTop ℝ≥0)))
    (hσle : ∀ k ω, σ k ω ≤ τ ω) :
    ∀ k (ρ : Ω → ℝ≥0)
      (hρstop : IsStoppingTime 𝓕.rightCont
        (fun ω => (ρ ω : WithTop ℝ≥0)))
      (hρle : ∀ ω, ρ ω ≤ σ k ω)
      (δ : ℝ) (hδ : 0 < δ)
      (hFloor : ∀ ω (t : ℝ≥0), 0 < t → t < ρ ω →
        δ ≤ riskProcess X x D t ω)
      (A : Set Ω), MeasurableSet[𝓕.rightCont 0] A →
    ∀ (j : ℕ),
      let U : ℕ → ℕ → Ω → ℝ := fun m i ω =>
        let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
        let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
        let a : ℝ := δ / 2
        let b : ℝ := C.toReal *
          (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
        let Y : ℕ → Ω → ℝ := fun i η =>
          x + X.X (s i) η - rightLimit D (s i) η
        let Z : ℕ → Ω → ℝ := fun i η =>
          X.X (s i + Δ) η - X.X (s i) η - (Δ : ℝ) * X.c
        let G : ℕ → Ω → ℝ := fun i η =>
          if s i < ρ η then Real.exp (-(q * (s i : ℝ))) *
            (if Y i η ∈ Icc a b then deriv w (Y i η) else 1)
          else 0
        let H : ℕ → Ω → ℝ := fun i η =>
          if s i < ρ η then (1 / 2 : ℝ) *
            Real.exp (-(q * (s i : ℝ))) *
            (if Y i η ∈ Icc a b then iteratedDeriv 2 w (Y i η) else 0)
          else 0
        H i ω * (Z i ω ^ 2 - (Δ : ℝ) * X.σ ^ 2)
      ∀ m : ℕ, ∀ i : ℕ, i ≤ m →
        let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        let a : ℝ := δ / 2
        let b : ℝ := C.toReal *
          (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
        let Y : Ω → ℝ := fun ω =>
          x + X.X s ω - rightLimit D s ω
        let H : Ω → ℝ := fun ω =>
          if s < ρ ω then (1 / 2 : ℝ) *
            Real.exp (-(q * (s : ℝ))) *
            (if Y ω ∈ Icc a b then iteratedDeriv 2 w (Y ω) else 0)
          else 0
        StronglyMeasurable[𝓕.rightCont s] H := by
  intro k ρ hρstop hρle δ hδ hFloor A hA j U m i hi
  let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
  let s : ℝ≥0 := (i : ℝ≥0) * Δ
  let a : ℝ := δ / 2
  let b : ℝ := C.toReal *
    (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
  let Y : Ω → ℝ := fun ω => x + X.X s ω - rightLimit D s ω
  have hp : Measurable (fun y : ℝ => if y ∈ Icc a b then iteratedDeriv 2 w y else 0) :=
    avram_gb68_finitecap_compact_hessian_cutoff_measurable w C hC hFiniteCap hw_smooth δ hδ j
  have hXm : Measurable[𝓕.rightCont s] (X.X s) :=
    (X.adapted s).mono ((𝓕.le_rightCont) s) le_rfl
  have hDm : Measurable[𝓕.rightCont s] (fun ω => rightLimit D s ω) :=
    (dividendStrategy_rightLimit_adapted_rightCont D hD.1.1) s
  have hYm : Measurable[𝓕.rightCont s] Y :=
    (measurable_const.add hXm).sub hDm
  have hsm : MeasurableSet[𝓕.rightCont s] {ω : Ω | s < ρ ω} := by
    have heq : {ω : Ω | s < ρ ω} = {ω : Ω | (ρ ω : WithTop ℝ≥0) ≤ (s : WithTop ℝ≥0)}ᶜ := by
      ext ω
      simpa only [Set.mem_setOf_eq, Set.mem_compl_iff, WithTop.coe_le_coe] using
        (lt_iff_not_ge : s < ρ ω ↔ ¬ ρ ω ≤ s)
    rw [heq]
    exact (hρstop.measurableSet_le s).compl
  have ht : Measurable[𝓕.rightCont s] (fun ω => if s < ρ ω then
        (1 / 2 : ℝ) * Real.exp (-(q * (s : ℝ))) *
          (if Y ω ∈ Icc a b then iteratedDeriv 2 w (Y ω) else 0) else 0) :=
    Measurable.ite hsm (measurable_const.mul (hp.comp hYm)) measurable_const
  exact ht.stronglyMeasurable
