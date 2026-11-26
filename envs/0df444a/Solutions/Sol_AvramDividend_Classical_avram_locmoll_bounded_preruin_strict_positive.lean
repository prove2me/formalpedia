-- Prove2me | solution 1 for AvramDividend.Classical.avram_locmoll_bounded_preruin_strict_positive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T21:52:08.741362+00:00
-- url     : https://prove2.me/submissions/d2f8e336-079c-4ff2-9483-e8f83d167a7f

import Mathlib
import Theorems.Thm_AvramDividend_Classical_exists_countable_dense_nnreal_time_set_zero
import Theorems.Thm_AvramDividend_Classical_postPaymentReserve_cadlag_adapted
import Theorems.Thm_AvramDividend_Classical_avram_gclose15_original_negative_postpayment_usc
import Theorems.Thm_AvramDividend_Classical_avram_gbB31_generic_capped_closed_hit_isStoppingTime
import Theorems.Thm_AvramDividend_Classical_usc_capped_first_closed_hit_le_iff_prefix_hit
import Theorems.Thm_AvramDividend_Classical_avram_gclose16_original_rightcont_stopping_strict_postpayment_preruin
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (H : ℝ≥0) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≤ H → (t : ℝ≥0∞) < ruinTime X x D ω →
      0 < x + X.X t ω - rightLimit D t ω := by 
  obtain ⟨S, hS, hDense, h0⟩ := exists_countable_dense_nnreal_time_set_zero
  let U : ℝ≥0 → Ω → ℝ := fun t ω => -(x + X.X t ω - rightLimit D t ω)
  let L : ℝ≥0 := H + 1
  let τ : Ω → ℝ≥0 := fun ω =>
    sInf ((Icc 0 L ∩ (fun t => U t ω) ⁻¹' Ici 0) ∪ {L})
  have hcad := postPaymentReserve_cadlag_adapted X x D hD.1.1
  have husc : ∀ ω t, UpperSemicontinuousOn (fun s => U s ω) (Icc 0 t) :=
    avram_gclose15_original_negative_postpayment_usc X x D hD.1.1
  have hstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)) :=
    avram_gbB31_generic_capped_closed_hit_isStoppingTime U hcad.2.2.neg
      (fun ω t => (hcad.1 ω t).neg) husc S hS hDense h0 L 0
  have hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s} := by
    intro s
    simpa only [WithTop.coe_le_coe] using hstop s
  have hp := avram_gclose16_original_rightcont_stopping_strict_postpayment_preruin
    X hBV x C D hD τ hτ hstop
  filter_upwards [hp] with ω hω
  intro t ht htr
  by_contra! hbad
  have htL : t < L := lt_of_le_of_lt ht (by dsimp [L]; exact lt_add_of_pos_right H zero_lt_one)
  have hτt : τ ω ≤ t :=
    (usc_capped_first_closed_hit_le_iff_prefix_hit
      (fun s => U s ω) L t 0 (husc ω L) htL).2 ⟨t, le_rfl, by dsimp [U]; linarith⟩
  have hτL : τ ω < L := hτt.trans_lt htL
  have hτruin : (τ ω : ℝ≥0∞) < ruinTime X x D ω :=
    (ENNReal.coe_le_coe.mpr hτt).trans_lt htr
  have hstrict := hω hτruin
  obtain ⟨s, hs, hsu⟩ := (usc_capped_first_closed_hit_le_iff_prefix_hit
    (fun a => U a ω) L (τ ω) 0 (husc ω L) hτL).1 le_rfl
  have hτs : τ ω ≤ s := (usc_capped_first_closed_hit_le_iff_prefix_hit
    (fun a => U a ω) L s 0 (husc ω L) (hs.trans_lt hτL)).2
      ⟨s, le_rfl, hsu⟩
  have hst : s = τ ω := le_antisymm hs hτs
  rw [hst] at hsu
  dsimp [U] at hsu
  linarith
