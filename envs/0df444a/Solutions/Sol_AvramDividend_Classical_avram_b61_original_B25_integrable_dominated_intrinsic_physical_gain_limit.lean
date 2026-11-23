-- Prove2me | solution 1 for AvramDividend.Classical.avram_b61_original_B25_integrable_dominated_intrinsic_physical_gain_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T08:58:42.528645+00:00
-- url     : https://prove2.me/submissions/d534d7a7-d087-4e6b-a2a2-6e72e5028d9b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option pp.explicit false
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (G : ℕ → Ω → ℝ) (MG BG : Ω → ℝ)
    (hMeas : ∀ k, AEStronglyMeasurable (G k) P)
    (hBG : Integrable BG P)
    (hDom : ∀ᵐ ω ∂P, ∀ k, ‖G k ω‖ ≤ BG ω)
    (hLim : ∀ᵐ ω ∂P,
      Tendsto (fun k => G k ω) atTop (𝓝 (MG ω))) :
    Integrable MG P := by
  have hMGmeas : AEStronglyMeasurable MG P :=
    aestronglyMeasurable_of_tendsto_ae atTop hMeas hLim
  refine Integrable.mono hBG hMGmeas ?_
  filter_upwards [hDom, hLim] with ω hd hl
  have hnorm :
      Tendsto (fun k : ℕ => ‖G k ω‖)
        atTop (𝓝 ‖MG ω‖) :=
    continuous_norm.tendsto (MG ω) |>.comp hl
  have hBound : ‖MG ω‖ ≤ BG ω :=
    le_of_tendsto hnorm (Filter.Eventually.of_forall hd)
  exact le_trans hBound (by simpa [Real.norm_eq_abs] using
    (le_abs_self (BG ω)))
