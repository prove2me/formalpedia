-- Prove2me | solution 1 for AvramDividend.Classical.avram_a21_original_simple_stage_intensity_energy_20261113
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T07:21:24.92388+00:00
-- url     : https://prove2.me/submissions/f23426fd-a4aa-48a8-b7d1-12b77bec8a3c

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_simple_nat_stage_exact_energy_20261112
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_bounded_borel_mark_centered_isometry_20261112
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology BigOperators
noncomputable section

/-- A natural-indexed source physical simple-mark stage has exact squared
Levy intensity, via the original compensated marked-Poisson L2 isometry. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n m : ℕ) (hnm : n ≤ m) (t : ℝ≥0)
    (f : SimpleFunc ℝ ℝ)
    (hBound : ∀ z ∈ Ioc (-(1 / ((n : ℝ) + 1)))
       (-(1 / ((m : ℝ) + 1))), |f z| ≤ 1) :
    let S : Set ℝ := Ioc (-(1 / ((n : ℝ) + 1)))
       (-(1 / ((m : ℝ) + 1)))
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
        ∑ i ∈ Finset.range K, c i *
          ((NX ω (Ioc 0 t ×ˢ B i)).toReal -
            (((t : ℝ≥0∞) * X.ν (B i)).toReal))
      let E : ℝ :=
        ∑ i ∈ Finset.range K, (c i)^2 *
          (((t : ℝ≥0∞) * X.ν (B i)).toReal)
      (∀ᵐ ω ∂P, F ω =
        (∫ p in (Ioc 0 t ×ˢ S), f p.2 ∂NX ω) -
          (t : ℝ) * (∫ z in S, f z ∂X.ν)) ∧
      Integrable (fun ω => (F ω)^2) P ∧
      (∫ ω, (F ω)^2 ∂P) = E ∧
      E = (t : ℝ) * (∫ z in S, (f z)^2 ∂X.ν) := by
  classical
  let S : Set ℝ := Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
  have hS : MeasurableSet S := measurableSet_Ioc
  have hNeg : S ⊆ Iio (0 : ℝ) := by
    intro z hz
    have hp : 0 < 1 / ((m : ℝ) + 1) := by positivity
    exact lt_of_le_of_lt hz.2 (by linarith)
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  let J : Ω → ℝ := fun ω => ∫ p in (Ioc 0 t ×ˢ S), f p.2 ∂NX ω
  let r : ℝ := (t : ℝ) * (∫ z in S, f z ∂X.ν)
  let q : ℝ := (t : ℝ) * (∫ z in S, (f z)^2 ∂X.ν)
  obtain ⟨K, B, c, hB, hDisj, hAE, hFI, hFM⟩ :=
    avram_a21_original_simple_nat_stage_exact_energy_20261112
      X hFinite t S hS hNeg f hBound
  let F : Ω → ℝ := fun ω =>
    ∑ i ∈ Finset.range K, c i *
      ((NX ω (Ioc 0 t ×ˢ B i)).toReal -
        (((t : ℝ≥0∞) * X.ν (B i)).toReal))
  let E : ℝ := ∑ i ∈ Finset.range K, (c i)^2 *
    (((t : ℝ≥0∞) * X.ν (B i)).toReal)
  change (∀ᵐ ω ∂P, F ω = J ω - r) at hAE
  change Integrable (fun ω => (F ω)^2) P at hFI
  change (∫ ω, (F ω)^2 ∂P) = E at hFM
  have hIso := avram_a21_original_bounded_borel_mark_centered_isometry_20261112
    X hX hFinite n m hnm f f.measurable hBound t
  change Integrable (fun ω => (J ω-r)^2) P ∧
    (∫ ω, (J ω-r)^2 ∂P) = q at hIso
  have hEq : E = q := by
    calc
      E = ∫ ω, (F ω)^2 ∂P := hFM.symm
      _ = ∫ ω, (J ω-r)^2 ∂P := by
        apply integral_congr_ae
        filter_upwards [hAE] with ω hω
        rw [hω]
      _ = q := hIso.2
  exact ⟨K, B, c, hB, hDisj, hAE, hFI, hFM, hEq⟩
