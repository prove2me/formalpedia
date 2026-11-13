-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja33_original_disjoint_negative_borel_cells_cross_zero_20261111
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T09:59:00.445611+00:00
-- url     : https://prove2.me/submissions/6b6cb90d-c93c-466e-bacf-5cdf11d3243c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ja32_original_negative_borel_cell_exact_variance_20261111
import Theorems.Thm_AvramDividend_Classical_avram_a20_original_disjoint_negative_borel_real_count_add_ae
import Theorems.Thm_AvramDividend_Classical_avram_a20_centered_covariance_zero_from_additive_variances
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (A B : Set ℝ)
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hNegA : A ⊆ Iio (0 : ℝ)) (hNegB : B ⊆ Iio (0 : ℝ))
    (hDisj : Disjoint A B) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let rA : ℝ := ((T : ℝ≥0∞) * X.ν A).toReal
    let rB : ℝ := ((T : ℝ≥0∞) * X.ν B).toReal
    let YA : Ω → ℝ := fun ω =>
      (NX ω (Ioc 0 T ×ˢ A)).toReal - rA
    let YB : Ω → ℝ := fun ω =>
      (NX ω (Ioc 0 T ×ˢ B)).toReal - rB
    Integrable (fun ω => YA ω * YB ω) P ∧
      (∫ ω, YA ω * YB ω ∂P) = 0 := by
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  let R : Set ℝ → ℝ := fun C => ((T : ℝ≥0∞) * X.ν C).toReal
  let Y : Set ℝ → Ω → ℝ := fun C ω => (NX ω (Ioc 0 T ×ˢ C)).toReal - R C
  change Integrable (fun ω => Y A ω * Y B ω) P ∧
    (∫ ω, Y A ω * Y B ω ∂P) = 0
  have hV (C : Set ℝ) (hC : MeasurableSet C) (hNeg : C ⊆ Iio (0 : ℝ)) :
      Integrable (fun ω => (Y C ω) ^ 2) P ∧
      (∫ ω, (Y C ω) ^ 2 ∂P) = R C := by
    simpa only [Y, NX, R] using
      (avram_ja32_original_negative_borel_cell_exact_variance_20261111
        X hFinite T C hC hNeg)
  have hU : MeasurableSet (A ∪ B) := hA.union hB
  have hNegU : A ∪ B ⊆ Iio (0 : ℝ) := union_subset hNegA hNegB
  have hRate (C : Set ℝ) (hNeg : C ⊆ Iio (0 : ℝ)) :
      ((T : ℝ≥0∞) * X.ν C) ≠ ⊤ := by
    have hC : X.ν C < ⊤ :=
      lt_of_le_of_lt (measure_mono hNeg) (lt_top_iff_ne_top.mpr hFinite)
    exact ne_of_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top hC)
  have hR : R (A ∪ B) = R A + R B := by
    dsimp [R]
    rw [measure_union hDisj hB, mul_add,
      ENNReal.toReal_add (hRate A hNegA) (hRate B hNegB)]
  have hN : ∀ᵐ ω ∂P,
      (NX ω (Ioc 0 T ×ˢ (A ∪ B))).toReal =
      (NX ω (Ioc 0 T ×ˢ A)).toReal +
      (NX ω (Ioc 0 T ×ˢ B)).toReal := by
    simpa only [NX] using
      (avram_a20_original_disjoint_negative_borel_real_count_add_ae
        X hFinite T A B hA hB hNegA hNegB hDisj)
  have hY : ∀ᵐ ω ∂P, Y (A ∪ B) ω = Y A ω + Y B ω := by
    filter_upwards [hN] with ω hω
    dsimp [Y]
    rw [hω, hR]
    ring
  obtain ⟨hAI, hAM⟩ := hV A hA hNegA
  obtain ⟨hBI, hBM⟩ := hV B hB hNegB
  obtain ⟨hUI, hUM⟩ := hV (A ∪ B) hU hNegU
  exact avram_a20_centered_covariance_zero_from_additive_variances
    P (Y A) (Y B) (Y (A ∪ B)) (R A) (R B)
    hAI hBI hUI hY hAM hBM (by simpa only [hR] using hUM)
