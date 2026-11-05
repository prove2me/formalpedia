-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_discard_joint_unintegrable_signed_residuals
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T07:38:05.123637+00:00
-- url     : https://prove2.me/submissions/ae1d8a6b-8331-4c1b-883b-1786e821879d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_three_source_martingales
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Discard a jointly nonpositive source drift and control loss, with neither L1. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (w : ℝ → ℝ)
    (D : ℝ≥0 → Ω → ℝ) (τ : Ω → ℝ≥0)
    (W Cash Term : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hTerm : ∀ ω, Term ω =
      Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (Mc Ms Ml Rgen Rctrl : Ω → ℝ)
    (hc : Integrable Mc P) (hs : Integrable Ms P)
    (hl : Integrable Ml P)
    (hc0 : (∫ ω, Mc ω ∂P) = 0)
    (hs0 : (∫ ω, Ms ω ∂P) = 0)
    (hl0 : (∫ ω, Ml ω ∂P) = 0)
    (hjoint : ∀ᵐ ω ∂P, Rgen ω + Rctrl ω ≤ 0)
    (hIto : ∀ᵐ ω ∂P,
      Term ω + Cash ω ≤
        w x + Mc ω + Ms ω + Ml ω + Rgen ω + Rctrl ω) :
    ∃ M G H : Ω → ℝ,
      Integrable M P ∧ Integrable G P ∧ Integrable H P ∧
      (∫ ω, M ω ∂P) = 0 ∧
      (∀ᵐ ω ∂P, G ω + H ω ≤ 0) ∧
      (∀ᵐ ω ∂P,
        Term ω + Cash ω ≤ w x + M ω + G ω + H ω) := by
  have hz : Integrable (fun _ : Ω => (0 : ℝ)) P :=
    integrable_zero Ω ℝ P
  have hsign : ∀ᵐ ω ∂P, (0 : ℝ) + 0 ≤ 0 :=
    Filter.Eventually.of_forall (fun _ => by norm_num)
  have hupper : ∀ᵐ ω ∂P,
      Term ω + Cash ω ≤
        w x + Mc ω + Ms ω + Ml ω + (0 : ℝ) + 0 := by
    filter_upwards [hIto, hjoint] with ω hi hr
    linarith
  exact avram_p4_f_assembly_three_source_martingales
    w x Term Cash Mc Ms Ml (fun _ => 0) (fun _ => 0)
    hc hs hl hz hz hc0 hs0 hl0 hsign hupper
