-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_original_allcap_ennreal_expected_budget_implies_terminal_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T18:51:06.461189+00:00
-- url     : https://prove2.me/submissions/26627546-7d17-43a4-ad1c-3855ae8607a8

import Mathlib.Data.ENNReal.Real
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped ENNReal
noncomputable section

/-- A finite ENNReal original stopped reward bound forces terminal L¹,
even when the dividend cap is infinite and the payoff is unbounded. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (w : ℝ → ℝ) (x : ℝ) (hwx : 0 ≤ w x)
    (Term Cash : Ω → ℝ)
    (hTermMeas : AEStronglyMeasurable Term P)
    (hCashI : Integrable Cash P)
    (hTermPos : ∀ᵐ ω ∂P, 0 ≤ Term ω)
    (hCashPos : ∀ᵐ ω ∂P, 0 ≤ Cash ω)
    (hBound : (∫⁻ ω, ENNReal.ofReal (Term ω + Cash ω) ∂P) ≤
      ENNReal.ofReal (w x)) :
    Integrable Term P ∧
    (∫ ω, Term ω + Cash ω ∂P) ≤ w x := by
  have hSumPos : ∀ᵐ ω ∂P, 0 ≤ Term ω + Cash ω := by
    filter_upwards [hTermPos, hCashPos] with ω ht hc
    linarith
  have hSumMeas : AEStronglyMeasurable
      (fun ω => Term ω + Cash ω) P :=
    hTermMeas.add hCashI.aestronglyMeasurable
  have hSumFinite :
      (∫⁻ ω, ENNReal.ofReal (Term ω + Cash ω) ∂P) < ⊤ :=
    lt_of_le_of_lt hBound (by simp)
  have hSumI : Integrable (fun ω => Term ω + Cash ω) P :=
    ⟨hSumMeas, (hasFiniteIntegral_iff_ofReal hSumPos).2 hSumFinite⟩
  have hTermI : Integrable Term P := by
    have hd := hSumI.sub hCashI
    convert hd using 1
    ext ω
    simp
  refine ⟨hTermI, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hSumPos hSumMeas]
  exact ENNReal.toReal_le_of_le_ofReal hwx hBound
