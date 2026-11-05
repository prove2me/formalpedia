-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_a_assist_signed_tests_negative_borel_of_transport
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T09:02:16.753506+00:00
-- url     : https://prove2.me/submissions/821cfbbc-f180-4085-b187-e588eee659dd

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Restrict
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_assist_negative_subtype_compact_zero_extension
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_negative_cut_eq_of_subtype_compact_tests
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_assist_negative_cdf_determines_separated_borel
import Mathlib.Topology.ContinuousMap.CompactlySupported
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Topology AvramDividend.Classical

/-- Signed compact-negative tests determine separated Borel masses given exact subtype transport. -/
theorem solution
    (μ ν : Measure ℝ)
    (hμBand : ∀ δ : ℝ, 0 < δ → μ (Iic (-δ)) < ⊤)
    (hνBand : ∀ δ : ℝ, 0 < δ → ν (Iic (-δ)) < ⊤)
    (hSigned : ∀ (g : ℝ → ℝ), Continuous g →
      IsCompact (tsupport g) → tsupport g ⊆ Iio (0 : ℝ) →
      (∫ y, g y ∂μ) = (∫ y, g y ∂ν))
    (hTransportμ : ∀ (f : CompactlySupportedContinuousMap {x : ℝ // x < 0} ℝ)
        (g : ℝ → ℝ), tsupport g ⊆ Iio (0 : ℝ) →
      (∀ x : {x : ℝ // x < 0}, g (x : ℝ) = f x) →
      (∫ x, f x ∂(Measure.comap (Subtype.val : {x : ℝ // x < 0} → ℝ) μ)) =
        (∫ y, g y ∂μ))
    (hTransportν : ∀ (f : CompactlySupportedContinuousMap {x : ℝ // x < 0} ℝ)
        (g : ℝ → ℝ), tsupport g ⊆ Iio (0 : ℝ) →
      (∀ x : {x : ℝ // x < 0}, g (x : ℝ) = f x) →
      (∫ x, f x ∂(Measure.comap (Subtype.val : {x : ℝ // x < 0} → ℝ) ν)) =
        (∫ y, g y ∂ν))
    (B : Set ℝ) (hB : MeasurableSet B)
    (ε : ℝ) (hε : 0 < ε) (hBsep : B ⊆ Iic (-ε)) :
    μ B = ν B := by
  have hSubtype :
      ∀ f : CompactlySupportedContinuousMap {x : ℝ // x < 0} ℝ,
        (∫ x, f x ∂(Measure.comap
          (Subtype.val : {x : ℝ // x < 0} → ℝ) μ)) =
        (∫ x, f x ∂(Measure.comap
          (Subtype.val : {x : ℝ // x < 0} → ℝ) ν)) := by
    intro f
    obtain ⟨g, hg, hc, hneg, hagree⟩ :=
      avram_p2_a_assist_negative_subtype_compact_zero_extension f
    calc
      _ = (∫ y, g y ∂μ) := hTransportμ f g hneg hagree
      _ = (∫ y, g y ∂ν) := hSigned g hg hc hneg
      _ = _ := (hTransportν f g hneg hagree).symm
  have hCuts (δ : ℝ) (hδ : 0 < δ) :
      μ (Iic (-δ)) = ν (Iic (-δ)) :=
    avram_p2_a_zero_rate_negative_cut_eq_of_subtype_compact_tests
      μ ν hμBand hνBand hSubtype δ hδ
  exact avram_p2_a_assist_negative_cdf_determines_separated_borel
    μ ν hμBand hCuts B hB ε hε hBsep
