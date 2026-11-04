-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_original_MGH_global_L1_from_random_envelopes
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T15:12:10.20245+00:00
-- url     : https://prove2.me/submissions/66c613fd-750e-46d7-a328-16177556e828

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- Each of three actual original stopped signed residuals is L¹ under a genuine integrable random envelope. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (M G H BM BG BH : Ω → ℝ)
    (hMm : AEStronglyMeasurable M P)
    (hGm : AEStronglyMeasurable G P)
    (hHm : AEStronglyMeasurable H P)
    (hBM : Integrable BM P) (hBG : Integrable BG P)
    (hBH : Integrable BH P)
    (hMb : ∀ᵐ ω ∂P, ‖M ω‖ ≤ ‖BM ω‖)
    (hGb : ∀ᵐ ω ∂P, ‖G ω‖ ≤ ‖BG ω‖)
    (hHb : ∀ᵐ ω ∂P, ‖H ω‖ ≤ ‖BH ω‖) :
    Integrable M P ∧ Integrable G P ∧ Integrable H P := by
  exact ⟨Integrable.mono hBM hMm hMb,
    Integrable.mono hBG hGm hGb,
    Integrable.mono hBH hHm hHb⟩
