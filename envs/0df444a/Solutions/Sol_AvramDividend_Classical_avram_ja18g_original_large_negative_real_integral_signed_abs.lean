-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18g_original_large_negative_real_integral_signed_abs
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T03:12:37.442245+00:00
-- url     : https://prove2.me/submissions/58c0f976-21b5-4c03-8c29-7e372cb0a7bb

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ja18g_original_large_negative_signed_mark_integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Negative large Levy marks have real integral minus their absolute ENNReal mass. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    (∫ z in Iic (-1 : ℝ), z ∂X.ν) =
      - (∫⁻ z in Iic (-1 : ℝ), ENNReal.ofReal |z| ∂X.ν).toReal := by
  let B : Set ℝ := Iic (-1 : ℝ)
  have hSigned : IntegrableOn (fun z : ℝ => z) B X.ν := by
    simpa only [B] using
      (avram_ja18g_original_large_negative_signed_mark_integrable X hX)
  have hAbs : IntegrableOn (fun z : ℝ => |z|) B X.ν := by
    change Integrable (fun z : ℝ => |z|) (X.ν.restrict B)
    simpa [Real.norm_eq_abs] using hSigned.norm
  have hAbsNonneg : 0 ≤ᵐ[X.ν.restrict B] (fun z : ℝ => |z|) :=
    Filter.Eventually.of_forall (fun z => abs_nonneg z)
  have hAbsIntegralNonneg : 0 ≤ (∫ z in B, |z| ∂X.ν) :=
    integral_nonneg (fun z => abs_nonneg z)
  have hBridge : (∫ z in B, |z| ∂X.ν) =
      (∫⁻ z in B, ENNReal.ofReal |z| ∂X.ν).toReal := by
    rw [← ofReal_integral_eq_lintegral_ofReal hAbs hAbsNonneg,
      ENNReal.toReal_ofReal hAbsIntegralNonneg]
  have hSignedAbs : (∫ z in B, z ∂X.ν) =
      - (∫ z in B, |z| ∂X.ν) := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Iic] with z hz
    have hz0 : z ≤ 0 := le_trans hz (by norm_num)
    simp only [abs_of_nonpos hz0]
    ring
  calc
    (∫ z in Iic (-1 : ℝ), z ∂X.ν) =
        - (∫ z in B, |z| ∂X.ν) := hSignedAbs
    _ = - (∫⁻ z in B, ENNReal.ofReal |z| ∂X.ν).toReal := by
      rw [hBridge]
