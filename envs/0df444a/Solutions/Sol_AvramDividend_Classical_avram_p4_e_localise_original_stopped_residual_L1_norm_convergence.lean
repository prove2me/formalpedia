-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_original_stopped_residual_L1_norm_convergence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:51:28.02798+00:00
-- url     : https://prove2.me/submissions/deab927d-4289-4a18-bbfe-79d5f483b942

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open AvramDividend.Classical

/-- Genuine L¹ norm convergence of the original stopped residual under one source-path envelope. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (Mk : ℕ → Ω → ℝ) (M B : Ω → ℝ)
    (hMkMeas : ∀ k, AEStronglyMeasurable (Mk k) P)
    (hMMeas : AEStronglyMeasurable M P)
    (hBInt : Integrable B P)
    (hBound : ∀ k, ∀ᵐ ω ∂P, ‖Mk k ω‖ ≤ B ω)
    (hAs : ∀ᵐ ω ∂P, Tendsto (fun k => Mk k ω) atTop (𝓝 (M ω))) :
    Integrable M P ∧
    Tendsto (fun k => ∫ ω, ‖Mk k ω - M ω‖ ∂P) atTop (𝓝 (0 : ℝ)) := by
  have hAll : ∀ᵐ ω ∂P, ∀ k, ‖Mk k ω‖ ≤ B ω :=
    ae_all_iff.mpr hBound
  have hLimitBound : ∀ᵐ ω ∂P, ‖M ω‖ ≤ ‖B ω‖ := by
    filter_upwards [hAll, hAs] with ω hb hlim
    have hn : Tendsto (fun k => ‖Mk k ω‖) atTop (𝓝 ‖M ω‖) :=
      (continuous_norm.tendsto (M ω)).comp hlim
    exact (le_of_tendsto hn (Filter.Eventually.of_forall hb)).trans
      (le_abs_self (B ω))
  have hMint : Integrable M P := Integrable.mono hBInt hMMeas hLimitBound
  have hDiffMeas : ∀ k, AEStronglyMeasurable
      (fun ω => ‖Mk k ω - M ω‖) P := by
    intro k
    exact ((hMkMeas k).sub hMMeas).norm
  have hEnvelopeInt : Integrable (fun ω => 2 * ‖B ω‖) P :=
    hBInt.norm.const_mul 2
  have hDiffBound : ∀ k, ∀ᵐ ω ∂P,
      ‖‖Mk k ω - M ω‖‖ ≤ 2 * ‖B ω‖ := by
    intro k
    filter_upwards [hBound k, hLimitBound] with ω hb hm
    have ht : ‖Mk k ω - M ω‖ ≤ ‖Mk k ω‖ + ‖M ω‖ :=
      norm_sub_le _ _
    have hu : ‖Mk k ω‖ + ‖M ω‖ ≤ 2 * ‖B ω‖ := by
      have hreal : B ω ≤ ‖B ω‖ := le_abs_self (B ω)
      nlinarith
    simpa only [norm_norm] using ht.trans hu
  have hDiffAs : ∀ᵐ ω ∂P,
      Tendsto (fun k => ‖Mk k ω - M ω‖) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [hAs] with ω hlim
    have hconst : Tendsto (fun _ : ℕ => M ω) atTop (𝓝 (M ω)) :=
      tendsto_const_nhds
    have hd := hlim.sub hconst
    simpa only [sub_self, norm_zero] using hd.norm
  have hDCT : Tendsto
      (fun k => ∫ ω, ‖Mk k ω - M ω‖ ∂P) atTop
      (𝓝 (∫ ω, (0 : ℝ) ∂P)) :=
    tendsto_integral_of_dominated_convergence
      (fun ω => 2 * ‖B ω‖) hDiffMeas hEnvelopeInt hDiffBound hDiffAs
  exact ⟨hMint, by simpa only [integral_zero] using hDCT⟩
