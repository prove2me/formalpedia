-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_original_joint_stopped_L1_mean_and_signed_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:43:39.9036+00:00
-- url     : https://prove2.me/submissions/db75c4a3-7d2d-487d-a00b-4b8193bea7e2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open AvramDividend.Classical

/-- Original-source joint L¹ limit of genuine stopped martingale and signed drift terms. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (Mk Gk Hk : ℕ → Ω → ℝ) (M G H BM BG BH : Ω → ℝ)
    (hMkMeas : ∀ k, AEStronglyMeasurable (Mk k) P)
    (hMMeas : AEStronglyMeasurable M P)
    (hGMeas : AEStronglyMeasurable G P)
    (hHMeas : AEStronglyMeasurable H P)
    (hBMInt : Integrable BM P) (hBGInt : Integrable BG P)
    (hBHInt : Integrable BH P)
    (hMBound : ∀ k, ∀ᵐ ω ∂P, ‖Mk k ω‖ ≤ BM ω)
    (hGBound : ∀ k, ∀ᵐ ω ∂P, ‖Gk k ω‖ ≤ BG ω)
    (hHBound : ∀ k, ∀ᵐ ω ∂P, ‖Hk k ω‖ ≤ BH ω)
    (hMlim : ∀ᵐ ω ∂P, Tendsto (fun k => Mk k ω) atTop (𝓝 (M ω)))
    (hGlim : ∀ᵐ ω ∂P, Tendsto (fun k => Gk k ω) atTop (𝓝 (G ω)))
    (hHlim : ∀ᵐ ω ∂P, Tendsto (fun k => Hk k ω) atTop (𝓝 (H ω)))
    (hCentred : ∀ k, (∫ ω, Mk k ω ∂P) = 0)
    (hSign : ∀ k, ∀ᵐ ω ∂P, Gk k ω + Hk k ω ≤ 0) :
    Integrable M P ∧ Integrable G P ∧ Integrable H P ∧
    (∫ ω, M ω ∂P) = 0 ∧ (∀ᵐ ω ∂P, G ω + H ω ≤ 0) := by
  have hLimitBound (Fk : ℕ → Ω → ℝ) (F B : Ω → ℝ)
      (hBound : ∀ k, ∀ᵐ ω ∂P, ‖Fk k ω‖ ≤ B ω)
      (hLim : ∀ᵐ ω ∂P, Tendsto (fun k => Fk k ω) atTop (𝓝 (F ω))) :
      ∀ᵐ ω ∂P, ‖F ω‖ ≤ ‖B ω‖ := by
    have hAll : ∀ᵐ ω ∂P, ∀ k, ‖Fk k ω‖ ≤ B ω :=
      ae_all_iff.mpr hBound
    filter_upwards [hAll, hLim] with ω hω hlim
    have hnorm : Tendsto (fun k => ‖Fk k ω‖) atTop (𝓝 ‖F ω‖) :=
      (continuous_norm.tendsto (F ω)).comp hlim
    exact (le_of_tendsto hnorm (Filter.Eventually.of_forall hω)).trans
      (le_abs_self (B ω))
  have hMI : Integrable M P :=
    Integrable.mono hBMInt hMMeas (hLimitBound Mk M BM hMBound hMlim)
  have hGI : Integrable G P :=
    Integrable.mono hBGInt hGMeas (hLimitBound Gk G BG hGBound hGlim)
  have hHI : Integrable H P :=
    Integrable.mono hBHInt hHMeas (hLimitBound Hk H BH hHBound hHlim)
  have hConv :
      Tendsto (fun k => ∫ ω, Mk k ω ∂P) atTop (𝓝 (∫ ω, M ω ∂P)) :=
    tendsto_integral_of_dominated_convergence BM hMkMeas hBMInt hMBound hMlim
  have hConst :
      Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 (∫ ω, M ω ∂P)) := by
    simpa only [hCentred] using hConv
  have hZero : (∫ ω, M ω ∂P) = 0 :=
    (tendsto_nhds_unique tendsto_const_nhds hConst).symm
  have hSigns : ∀ᵐ ω ∂P, ∀ k, Gk k ω + Hk k ω ≤ 0 :=
    ae_all_iff.mpr hSign
  have hLimitSign : ∀ᵐ ω ∂P, G ω + H ω ≤ 0 := by
    filter_upwards [hSigns, hGlim, hHlim] with ω hs hg hh
    exact le_of_tendsto (hg.add hh) (Filter.Eventually.of_forall hs)
  exact ⟨hMI, hGI, hHI, hZero, hLimitSign⟩
