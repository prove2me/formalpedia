-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_original_exact_terminal_L1_of_signed_budget_and_initial_constant_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T16:26:05.375543+00:00
-- url     : https://prove2.me/submissions/d62c765a-36e7-458f-81a6-6df765025ea2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_anycap_payoff_nonnegative_from_source_interior_gradient
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_discounted_terminal_nonnegative_of_cap_payoff_sign
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- The exact source signed stopped budget forces terminal L¹ from its sign and integrable M,G,H,Cash. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (hxc : ENNReal.ofReal x ≤ C)
    (q : ℝ) (τ : Ω → ℝ≥0) (W : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (w : ℝ → ℝ) (hw0 : 0 ≤ w 0)
    (hwCont : ContinuousOn w (Ici (0 : ℝ)))
    (hwNeg : ∀ y : ℝ, y < 0 → w y = 0)
    (hwSmooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hwGrad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (Term Cash M G H : Ω → ℝ)
    (hTerm : ∀ ω, Term ω =
      Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (hTermMeas : AEStronglyMeasurable Term P)
    (hConstI : Integrable (fun _ : Ω => w x) P)
    (hCashI : Integrable Cash P)
    (hMI : Integrable M P) (hGI : Integrable G P)
    (hHI : Integrable H P)
    (hBudget : ∀ᵐ ω ∂P,
      Term ω + Cash ω ≤ w x + M ω + G ω + H ω) :
    Integrable Term P := by
  have hwCap :=
    avram_p4_e_localise_original_anycap_payoff_nonnegative_from_source_interior_gradient
      w C hw0 hwCont hwSmooth hwGrad
  have hPos :=
    avram_p4_e_localise_original_discounted_terminal_nonnegative_of_cap_payoff_sign
      X x C D hD hxc q τ W hW w hwNeg hwCap
  have hUpperI : Integrable
      (fun ω => w x + M ω + G ω + H ω - Cash ω) P :=
    (((hConstI.add hMI).add hGI).add hHI).sub hCashI
  apply Integrable.mono hUpperI hTermMeas
  filter_upwards [hBudget] with ω hω
  have ht : 0 ≤ Term ω := by
    rw [hTerm ω]
    exact hPos ω
  have hb : Term ω ≤ w x + M ω + G ω + H ω - Cash ω := by
    linarith
  have hub : 0 ≤ w x + M ω + G ω + H ω - Cash ω :=
    le_trans ht hb
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg ht, abs_of_nonneg hub]
  exact hb