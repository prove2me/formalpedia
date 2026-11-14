-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja28_original_borel_mark_simple_energy_certificate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T07:26:38.271044+00:00
-- url     : https://prove2.me/submissions/afa38388-cff9-4216-8608-f77864c17786

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a21_bounded_real_simple_mark_approx
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_simple_family_disjoint_energy_20261113
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_compensated_bounded_simple_mark_ae_limit_20261113
import Theorems.Thm_AvramDividend_Classical_avram_a21_source_compensated_simple_family_l2_envelope_20261113
import Theorems.Thm_AvramDividend_Classical_avram_a21_ae_equal_stages_square_envelope_transfer_20261113
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_bounded_borel_mark_centered_isometry_20261112
import Theorems.Thm_AvramDividend_Classical_avram_a20_bounded_Borel_mark_first_second_integral_limits
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology BigOperators
noncomputable section

/-- Exact original marked Poisson finite-strip square certificate from
genuine finite disjoint Borel mark cells and common source L2 domination. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ (n m : ℕ), n ≤ m → ∀ (t : ℝ≥0),
      let S : Set ℝ := Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
      let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
        ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      let C : Ω → ℝ := fun ω => (∫ p in (Ioc 0 t ×ˢ S), p.2 ∂NX ω) - (t : ℝ) * (∫ z in S, z ∂X.ν)
      let e : ℝ := (t : ℝ) * (∫ z in S, z ^ 2 ∂X.ν)
      ∃ (K : ℕ → ℕ) (B : ℕ → ℕ → Set ℝ) (c : ℕ → ℕ → ℝ) (g : Ω → ℝ),
        let F : ℕ → Ω → ℝ := fun k ω => ∑ i ∈ Finset.range (K k), c k i *
          ((NX ω (Ioc 0 t ×ˢ B k i)).toReal - (((t : ℝ≥0∞) * X.ν (B k i)).toReal))
        let E : ℕ → ℝ := fun k => ∑ i ∈ Finset.range (K k), (c k i) ^ 2 * (((t : ℝ≥0∞) * X.ν (B k i)).toReal)
        (∀ k, ∀ i ∈ Finset.range (K k), MeasurableSet (B k i) ∧ B k i ⊆ S) ∧
        (∀ k, ∀ i ∈ Finset.range (K k), ∀ j ∈ Finset.range (K k), i ≠ j → Disjoint (B k i) (B k j)) ∧
        (∀ k, AEStronglyMeasurable (fun ω => (F k ω) ^ 2) P) ∧
        Integrable g P ∧ (∀ k, ∀ᵐ ω ∂P, ‖(F k ω) ^ 2‖ ≤ g ω) ∧
        (∀ᵐ ω ∂P, Tendsto (fun k => (F k ω) ^ 2) atTop (𝓝 ((C ω) ^ 2))) ∧
        (∀ k, (∫ ω, (F k ω) ^ 2 ∂P) = E k) ∧
        Tendsto E atTop (𝓝 e) := by
  classical
  intro n m hnm t
  let S : Set ℝ := Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ X.X u ω -
      Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  let C : Ω → ℝ := fun ω => (∫ p in (Ioc 0 t ×ˢ S), p.2 ∂NX ω) - (t : ℝ) * (∫ z in S, z ∂X.ν)
  let e : ℝ := (t : ℝ) * (∫ z in S, z ^ 2 ∂X.ν)
  let D : Ω → ℝ := fun ω => (NX ω (Ioc 0 t ×ˢ S)).toReal + (((t : ℝ≥0∞) * X.ν S).toReal)
  obtain ⟨f, hfBound, hfLimit⟩ := avram_a21_bounded_real_simple_mark_approx
  let Z : ℕ → Ω → ℝ := fun k ω => (∫ p in (Ioc 0 t ×ˢ S), f k p.2 ∂NX ω) -
    (t : ℝ) * (∫ z in S, f k z ∂X.ν)
  have hS : MeasurableSet S := measurableSet_Ioc
  have hmpos : 0 < 1 / ((m : ℝ) + 1) := by positivity
  have hnpos : 0 < (n : ℝ) + 1 := by positivity
  have hnfrac : 1 / ((n : ℝ) + 1) ≤ 1 := by
    apply (div_le_iff₀ hnpos).mpr
    have hnc : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    nlinarith
  have hNeg : S ⊆ Iio (0 : ℝ) := by
    intro z hz; exact lt_of_le_of_lt hz.2 (by linarith)
  have hSub : S ⊆ Icc (-1 : ℝ) 0 := by
    intro z hz
    constructor
    · have hzl : -(1 / ((n : ℝ) + 1)) < z := hz.1
      linarith
    · exact le_of_lt (hNeg hz)
  have hBound : ∀ k z, z ∈ S → |f k z| ≤ 1 := fun k z hz => hfBound k z
  have hLimit : ∀ z ∈ S, Tendsto (fun k => f k z) atTop (𝓝 z) := fun z hz => hfLimit z (hSub hz)
  obtain ⟨K, B, c, hB, hDisj, hAE, hInt, hMom⟩ :=
    avram_a21_original_simple_family_disjoint_energy_20261113 X hFinite t S hS hNeg f hBound
  let F : ℕ → Ω → ℝ := fun k ω => ∑ i ∈ Finset.range (K k), c k i *
    ((NX ω (Ioc 0 t ×ˢ B k i)).toReal - (((t : ℝ≥0∞) * X.ν (B k i)).toReal))
  let E : ℕ → ℝ := fun k => ∑ i ∈ Finset.range (K k), (c k i)^2 * (((t : ℝ≥0∞) * X.ν (B k i)).toReal)
  change ∀ k, ∀ᵐ ω ∂P, F k ω = Z k ω at hAE
  change ∀ k, Integrable (fun ω => (F k ω)^2) P at hInt
  change ∀ k, (∫ ω, (F k ω)^2 ∂P) = E k at hMom
  have hEnvelope := avram_a21_source_compensated_simple_family_l2_envelope_20261113 X hFinite t S hS hNeg f hBound
  change Integrable (fun ω => (D ω)^2) P ∧ (∀ k, ∀ᵐ ω ∂P, ‖Z k ω‖ ≤ D ω) at hEnvelope
  have hConv := avram_a21_original_compensated_bounded_simple_mark_ae_limit_20261113 X hFinite t S hS hNeg (fun z => z) f hBound hLimit
  change ∀ᵐ ω ∂P, Tendsto (fun k => Z k ω) atTop (𝓝 (C ω)) at hConv
  obtain ⟨hMeas, hG, hDom, hSqLim⟩ :=
    avram_a21_ae_equal_stages_square_envelope_transfer_20261113 P F Z C D hInt hAE hEnvelope.2 hEnvelope.1 hConv
  have hEnergy : ∀ k, E k = (t : ℝ) * (∫ z in S, (f k z)^2 ∂X.ν) := by
    intro k
    have hIso := avram_a21_original_bounded_borel_mark_centered_isometry_20261112
      X hX hFinite n m hnm (f k) (f k).measurable (fun z hz => hBound k z hz) t
    change Integrable (fun ω => (Z k ω)^2) P ∧
      (∫ ω, (Z k ω)^2 ∂P) = (t : ℝ) * (∫ z in S, (f k z)^2 ∂X.ν) at hIso
    calc
      E k = (∫ ω, (F k ω)^2 ∂P) := (hMom k).symm
      _ = (∫ ω, (Z k ω)^2 ∂P) := by
        apply integral_congr_ae
        filter_upwards [hAE k] with ω he; rw [he]
      _ = _ := hIso.2
  have hMass : X.ν S < ⊤ := lt_of_le_of_lt (measure_mono hNeg) (lt_top_iff_ne_top.mpr hFinite)
  have hRate := avram_a20_bounded_Borel_mark_first_second_integral_limits X.ν S hS hMass (fun z => z) f hBound hLimit
  have hELimit : Tendsto E atTop (𝓝 e) := by
    have hMul : Tendsto (fun k => (t : ℝ) * (∫ z in S, (f k z)^2 ∂X.ν)) atTop
        (𝓝 ((t : ℝ) * (∫ z in S, z ^ 2 ∂X.ν))) := tendsto_const_nhds.mul hRate.2
    have he : E = fun k => (t : ℝ) * (∫ z in S, (f k z)^2 ∂X.ν) := by
      funext k; exact hEnergy k
    simpa only [he, e] using hMul
  exact ⟨K, B, c, (fun ω => (D ω)^2), hB, hDisj,
    hMeas, hG, hDom, hSqLim, hMom, hELimit⟩
