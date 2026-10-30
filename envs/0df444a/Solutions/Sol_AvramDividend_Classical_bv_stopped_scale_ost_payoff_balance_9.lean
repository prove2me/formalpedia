-- Prove2me | solution 9 for AvramDividend.Classical.bv_stopped_scale_ost_payoff_balance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T03:14:03.925398+00:00
-- url     : https://prove2.me/submissions/f09c2b53-897c-44e0-852e-31801235c684

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_strict_stopped_exit_payoff_lintegral_factorisation
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_value_eq_threshold
import Theorems.Thm_AvramDividend_Classical_bv_stopped_scale_ost_expectation_identity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

open AvramDividend.Classical

-- Payoff balance via Proved factorisation + Proved upcrossing value,
-- closed by the Open expectation identity 322217fe (coordinator-owned).
-- hcongr identifies the goal integrand (constant W a) with the
-- factorisation integrand (W (x + X stopped)); hFac rewrites that to
-- twoSidedExitExpectation * W a; hId closes the balance.
-- ProofCheckpoint: MATHEMATICAL_DECOMPOSITION. No local Lean was run.
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hBV : X.BoundedVariation)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    (∫⁻ ω, if twoSidedExitUpTime X (a - x) ω <
        twoSidedExitDownTime X (-x) ω then
      ENNReal.ofReal
        (Real.exp (-(q * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω)))) *
        ENNReal.ofReal (W a)
    else 0 ∂P) = ENNReal.ofReal (W x) := by
  have hFac :=
    AvramDividend.Classical.chat04_strict_stopped_exit_payoff_lintegral_factorisation
      X q a x hxa W
  have hb : 0 ≤ a - x := sub_nonneg.mpr hxa
  have hWval : ∀ ω : Ω,
      twoSidedExitUpTime X (a - x) ω < twoSidedExitDownTime X (-x) ω →
      W (x + X.X (twoSidedExitUpTime X (a - x) ω).toNNReal ω) = W a := by
    intro ω hwin
    have hfin : twoSidedExitUpTime X (a - x) ω ≠ ⊤ :=
      ne_of_lt (lt_of_lt_of_le hwin le_top)
    have hu : (((twoSidedExitUpTime X (a - x) ω).toNNReal : ℝ≥0) : ℝ≥0∞) =
        twoSidedExitUpTime X (a - x) ω :=
      ENNReal.coe_toNNReal hfin
    have hdef : twoSidedExitUpTime X (a - x) ω =
        ⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞) := rfl
    have hu_eq : (((twoSidedExitUpTime X (a - x) ω).toNNReal : ℝ≥0) : ℝ≥0∞) =
        ⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞) := hu.trans hdef
    have hXval : X.X (twoSidedExitUpTime X (a - x) ω).toNNReal ω = a - x :=
      AvramDividend.Classical.firstUpcrossing_value_eq_threshold
        X (a - x) hb ω _ hu_eq
    rw [hXval, add_sub_cancel]
  have hcongr : (∫⁻ ω, if twoSidedExitUpTime X (a - x) ω <
      twoSidedExitDownTime X (-x) ω then
    ENNReal.ofReal
      (Real.exp (-(q * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω)))) *
      ENNReal.ofReal
        (W (x + X.X (twoSidedExitUpTime X (a - x) ω).toNNReal ω))
    else 0 ∂P) =
    (∫⁻ ω, if twoSidedExitUpTime X (a - x) ω <
      twoSidedExitDownTime X (-x) ω then
    ENNReal.ofReal
      (Real.exp (-(q * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω)))) *
      ENNReal.ofReal (W a)
    else 0 ∂P) := by
    apply lintegral_congr_ae
    filter_upwards with ω
    by_cases hwin : twoSidedExitUpTime X (a - x) ω <
      twoSidedExitDownTime X (-x) ω
    · simp only [if_pos hwin]
      rw [hWval ω hwin]
    · simp only [if_neg hwin]
  have hId :=
    AvramDividend.Classical.bv_stopped_scale_ost_expectation_identity
      X hX q hq W hW hBV a x ha hx0 hxa
  rw [← hcongr, hFac]
  exact hId
