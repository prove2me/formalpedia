-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_piecewise_postpayment_caplinear_L1_from_discounted_Term
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T23:16:47.128389+00:00
-- url     : https://prove2.me/submissions/15191f16-5d86-4ba3-ab8a-fe801aed514a

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_public_original_anycap_book_postpayment_V_eq_w

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- A bounded original stopped clock removes the discount from the genuine
terminal L1 witness and transfers it to the cap-linear postpayment value. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hxc : ENNReal.ofReal x ≤ C)
    (q : ℝ) (hq : 0 ≤ q) (w V : ℝ → ℝ)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z else
        w C.toReal + (z - C.toReal))
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (τ : Ω → ℝ≥0) (H : ℝ≥0)
    (hτbound : ∀ ω, τ ω ≤ H)
    (hτmeas : Measurable (fun ω : Ω => (τ ω : ℝ)))
    (W Term : Ω → ℝ)
    (hW : ∀ ω, W ω = if τ ω = 0 ∨
      (τ ω : ℝ≥0∞) < ruinTime X x D ω then
      x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hTerm : ∀ ω, Term ω =
      Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (hTermI : Integrable Term P) :
    Integrable (fun ω => V (W ω)) P := by
  have hVw : ∀ ω, V (W ω) = w (W ω) := by
    intro ω
    have hs := avram_p3_c_bvchain_public_original_anycap_book_postpayment_V_eq_w
      X x C hC hxc w V hVtop hVfinite D hD ω (τ ω)
    rw [hW ω]
    split_ifs with h
    · exact hs.2
    · exact hs.1
  have hExpMeas : Measurable (fun ω : Ω =>
      Real.exp (q * (τ ω : ℝ))) :=
    Real.measurable_exp.comp (measurable_const.mul hτmeas)
  have hExpBound : ∀ᵐ ω ∂P,
      ‖Real.exp (q * (τ ω : ℝ))‖ ≤ Real.exp (q * (H : ℝ)) := by
    filter_upwards [] with ω
    have ht : (τ ω : ℝ) ≤ (H : ℝ) := by exact_mod_cast hτbound ω
    have hm : q * (τ ω : ℝ) ≤ q * (H : ℝ) :=
      mul_le_mul_of_nonneg_left ht hq
    simpa [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
      (Real.exp_le_exp.mpr hm)
  have hRescaled : Integrable
      (fun ω => Real.exp (q * (τ ω : ℝ)) * Term ω) P :=
    hTermI.bdd_mul hExpMeas.stronglyMeasurable.aestronglyMeasurable hExpBound
  have hFun : (fun ω => Real.exp (q * (τ ω : ℝ)) * Term ω) =
      (fun ω => V (W ω)) := by
    funext ω
    rw [hTerm ω, ← mul_assoc, ← Real.exp_add]
    have hc : q * (τ ω : ℝ) + -(q * (τ ω : ℝ)) = 0 := by ring
    simpa [hc] using (hVw ω).symm
  rw [hFun] at hRescaled
  exact hRescaled
