-- Prove2me | solution 1 for AvramDividend.Classical.avram_a21_original_simple_nat_stage_exact_energy_20261112
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T00:38:12.878825+00:00
-- url     : https://prove2.me/submissions/e0f8b7ac-59ff-448e-b5eb-fb9a3d2b365b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a21_simple_mark_natural_fibre_partition_20261112
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_simple_mark_fibre_centered_energy_20261112
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_simple_mark_fibre_compensated_identity_20261112
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology BigOperators
noncomputable section

/-- A genuine natural-indexed original marked Poisson finite stage has the
correct compensated physical integral and exact L2 squared-mark energy. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (S : Set ℝ)
    (hS : MeasurableSet S) (hNeg : S ⊆ Iio (0 : ℝ))
    (f : SimpleFunc ℝ ℝ) (hfBound : ∀ z ∈ S, |f z| ≤ 1) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    ∃ (K : ℕ) (B : ℕ → Set ℝ) (c : ℕ → ℝ),
      (∀ i ∈ Finset.range K, MeasurableSet (B i) ∧ B i ⊆ S) ∧
      (∀ i ∈ Finset.range K, ∀ j ∈ Finset.range K,
        i ≠ j → Disjoint (B i) (B j)) ∧
      let F : Ω → ℝ := fun ω =>
        ∑ i ∈ Finset.range K,
          c i * ((NX ω (Ioc 0 T ×ˢ B i)).toReal -
            (((T : ℝ≥0∞) * X.ν (B i)).toReal))
      let E : ℝ :=
        ∑ i ∈ Finset.range K,
          (c i)^2 * (((T : ℝ≥0∞) * X.ν (B i)).toReal)
      (∀ᵐ ω ∂P, F ω =
        (∫ p in (Ioc 0 T ×ˢ S), f p.2 ∂NX ω) -
          (T : ℝ) * (∫ z in S, f z ∂X.ν)) ∧
      Integrable (fun ω => (F ω)^2) P ∧
      (∫ ω, (F ω)^2 ∂P) = E := by
  classical
  obtain ⟨K, B, c, hB, hDisj, hSum, hFibres⟩ :=
    avram_a21_simple_mark_natural_fibre_partition_20261112 S hS f
  refine ⟨K, B, c, hB, hDisj, ?_⟩
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  let F : Ω → ℝ := fun ω =>
    ∑ i ∈ Finset.range K, c i *
      ((NX ω (Ioc 0 T ×ˢ B i)).toReal -
        (((T : ℝ≥0∞) * X.ν (B i)).toReal))
  let E : ℝ := ∑ i ∈ Finset.range K, (c i)^2 *
    (((T : ℝ≥0∞) * X.ν (B i)).toReal)
  let R : Ω → ℝ := fun ω => ∑ y ∈ f.range, y *
    ((NX ω (Ioc 0 T ×ˢ (S ∩ f ⁻¹' {y}))).toReal -
      (((T : ℝ≥0∞) * X.ν (S ∩ f ⁻¹' {y})).toReal))
  let v : ℝ := ∑ y ∈ f.range, y^2 *
    (((T : ℝ≥0∞) * X.ν (S ∩ f ⁻¹' {y})).toReal)
  have hFR : ∀ ω, F ω = R ω := by
    intro ω
    have hReindex := hSum (fun y : ℝ => y *
      ((NX ω (Ioc 0 T ×ˢ (S ∩ f ⁻¹' {y}))).toReal -
        (((T : ℝ≥0∞) * X.ν (S ∩ f ⁻¹' {y})).toReal)))
    change (∑ i ∈ Finset.range K, c i *
      ((NX ω (Ioc 0 T ×ˢ B i)).toReal -
        (((T : ℝ≥0∞) * X.ν (B i)).toReal))) = R ω
    calc
      _ = ∑ i ∈ Finset.range K, c i *
        ((NX ω (Ioc 0 T ×ˢ (S ∩ f ⁻¹' {c i}))).toReal -
          (((T : ℝ≥0∞) * X.ν (S ∩ f ⁻¹' {c i})).toReal)) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [hFibres i hi]
      _ = R ω := hReindex
  have hEv : E = v := by
    change (∑ i ∈ Finset.range K, (c i)^2 *
      (((T : ℝ≥0∞) * X.ν (B i)).toReal)) = v
    calc
      _ = ∑ i ∈ Finset.range K, (c i)^2 *
        (((T : ℝ≥0∞) * X.ν (S ∩ f ⁻¹' {c i})).toReal) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [hFibres i hi]
      _ = v := hSum (fun y => y^2 *
        (((T : ℝ≥0∞) * X.ν (S ∩ f ⁻¹' {y})).toReal))
  have hRmom :=
    avram_a21_original_simple_mark_fibre_centered_energy_20261112
      X hFinite T S hS hNeg f
  change Integrable (fun ω => (R ω)^2) P ∧
    (∫ ω, (R ω)^2 ∂P) = v at hRmom
  have hRid :=
    avram_a21_original_simple_mark_fibre_compensated_identity_20261112
      X hFinite T S hS hNeg f hfBound
  change ∀ᵐ ω ∂P, R ω =
    (∫ p in (Ioc 0 T ×ˢ S), f p.2 ∂NX ω) -
      (T : ℝ) * (∫ z in S, f z ∂X.ν) at hRid
  change (∀ᵐ ω ∂P, F ω =
    (∫ p in (Ioc 0 T ×ˢ S), f p.2 ∂NX ω) -
      (T : ℝ) * (∫ z in S, f z ∂X.ν)) ∧
    Integrable (fun ω => (F ω)^2) P ∧
    (∫ ω, (F ω)^2 ∂P) = E
  simpa only [hFR, hEv] using ⟨hRid, hRmom.1, hRmom.2⟩
