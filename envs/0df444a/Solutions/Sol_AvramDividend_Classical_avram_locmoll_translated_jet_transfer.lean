-- Prove2me | solution 1 for AvramDividend.Classical.avram_locmoll_translated_jet_transfer
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T21:42:30.138037+00:00
-- url     : https://prove2.me/submissions/f345c5bb-8338-4766-9311-475147b171c0

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_locmoll_compact_convolution_jet
open AvramDividend.Classical
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology Convolution
noncomputable section
set_option autoImplicit false
theorem solution
    (w V F ρ : ℝ → ℝ) (δ y : ℝ) (hδ : 0 < δ)
    (hρ : Integrable ρ)
    (hs : ∀ᵐ r ∂volume, ρ r ≠ 0 → r ∈ Icc (δ / 3) (2 * (δ / 3)))
    (hF : ContDiff ℝ 2 F) (hFc : HasCompactSupport F)
    (he : ∀ z ∈ Ioo (y - 5 * δ / 6) (y - δ / 6), F z = w z ∧ V z = w z) :
    Integrable (fun r => ρ r * w (y - r)) ∧
    Integrable (fun r => ρ r * deriv w (y - r)) ∧
    Integrable (fun r => ρ r * iteratedDeriv 2 w (y - r)) ∧
    (∫ r, ρ r * V (y - r)) = (∫ r, ρ r * w (y - r)) ∧
    deriv (fun t => ∫ r, ρ r * V (t - r)) y =
      (∫ r, ρ r * deriv w (y - r)) ∧
    iteratedDeriv 2 (fun t => ∫ r, ρ r * V (t - r)) y =
      (∫ r, ρ r * iteratedDeriv 2 w (y - r)) := by 
  let s := Ioo (y - 5 * δ / 6) (y - δ / 6)
  have hFw : EqOn F w s := fun z hz => (he z hz).1
  have hFD (n : ℕ) : EqOn (iteratedDeriv n F) (iteratedDeriv n w) s :=
    hFw.iteratedDeriv_of_isOpen isOpen_Ioo n
  have hweights (n : ℕ) :
      (fun r => ρ r * iteratedDeriv n F (y - r)) =ᵐ[volume]
      (fun r => ρ r * iteratedDeriv n w (y - r)) := by
    filter_upwards [hs] with r hr
    by_cases hz : ρ r = 0
    · simp [hz]
    · have hmem : y - r ∈ s := ⟨by linarith [(hr hz).2],
        by linarith [(hr hz).1]⟩
      rw [hFD n hmem]
  have hW := hweights 0
  have hD1 := hweights 1
  have hD2 := hweights 2
  simp only [iteratedDeriv_zero] at hW
  simp only [iteratedDeriv_one] at hD1
  have hnear : (fun t => ∫ r, ρ r * V (t - r)) =ᶠ[𝓝 y]
      (fun t => ∫ r, ρ r * F (t - r)) := by
    filter_upwards [Ioo_mem_nhds (show y - δ / 12 < y by linarith)
      (show y < y + δ / 12 by linarith)] with t ht
    apply integral_congr_ae
    filter_upwards [hs] with r hr
    by_cases hz : ρ r = 0
    · simp [hz]
    · have hh := he (t - r) ⟨by linarith [ht.1, (hr hz).2],
        by linarith [ht.2, (hr hz).1]⟩
      rw [hh.1, hh.2]
  obtain ⟨hI, hI1, hI2, hd1, hd2⟩ :=
    avram_locmoll_compact_convolution_jet ρ F hρ hF hFc y
  exact ⟨hI.congr hW, hI1.congr hD1, hI2.congr hD2,
    hnear.eq_of_nhds.trans (integral_congr_ae hW),
    hnear.deriv_eq.trans (hd1.trans (integral_congr_ae hD1)),
    (hnear.iteratedDeriv_eq 2).trans (hd2.trans (integral_congr_ae hD2))⟩
