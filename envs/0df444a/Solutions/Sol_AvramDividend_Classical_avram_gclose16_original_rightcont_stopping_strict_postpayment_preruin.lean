-- Prove2me | solution 1 for AvramDividend.Classical.avram_gclose16_original_rightcont_stopping_strict_postpayment_preruin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T22:17:15.75168+00:00
-- url     : https://prove2.me/submissions/d692a163-98a4-45f4-a253-c9bbb3a94e01

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gclose15_original_rightCont_UBV_downward_regular
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_preruin_postpayment_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendStrategy_rightLimit_monotone

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- At each genuine original right-continuous stopping time strictly before ruin,
the original controlled postpayment reserve is strictly solvent almost surely. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (hstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0))) :
    ∀ᵐ ω ∂P,
      (τ ω : ℝ≥0∞) < ruinTime X x D ω →
        0 < x + X.X (τ ω) ω - rightLimit D (τ ω) ω := by
  filter_upwards [
    avram_gclose15_original_rightCont_UBV_downward_regular
      X hBV τ hτ hstop
  ] with ω hdown
  intro hpre
  obtain ⟨u, htu, hur⟩ :=
    (ENNReal.lt_iff_exists_nnreal_btwn).mp hpre
  have htu' : τ ω < u := by
    exact_mod_cast htu
  let ε : ℝ≥0 := u - τ ω
  have hε : 0 < ε := tsub_pos_iff_lt.mpr htu'
  obtain ⟨s, hs, hsource⟩ := hdown ε hε
  have hτadd : τ ω + ε = u := add_tsub_cancel_of_le htu'.le
  have hsu : τ ω + s < u := by
    calc
      τ ω + s < τ ω + ε := by
        simpa [add_comm] using (add_lt_add_left hs (τ ω))
      _ = u := hτadd
  have hbefore : ((τ ω + s : ℝ≥0) : ℝ≥0∞) <
      ruinTime X x D ω := by
    exact lt_trans (by exact_mod_cast hsu) hur
  have hstart : 0 ≤ x + X.X (τ ω) ω - rightLimit D (τ ω) ω :=
    avram_p4_e_localise_preruin_postpayment_nonnegative
      X x C D hD ω (τ ω) (Or.inr hpre)
  have hfinish :
      0 ≤ x + X.X (τ ω + s) ω - rightLimit D (τ ω + s) ω :=
    avram_p4_e_localise_preruin_postpayment_nonnegative
      X x C D hD ω (τ ω + s) (Or.inr hbefore)
  have hmono : rightLimit D (τ ω) ω ≤ rightLimit D (τ ω + s) ω :=
    (avram_wave3_03_dividendStrategy_rightLimit_monotone
      D hD.1.1 ω) (le_add_of_nonneg_right (zero_le))
  linarith
