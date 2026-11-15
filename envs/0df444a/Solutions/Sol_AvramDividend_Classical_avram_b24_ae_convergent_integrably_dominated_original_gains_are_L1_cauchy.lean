-- Prove2me | solution 1 for AvramDividend.Classical.avram_b24_ae_convergent_integrably_dominated_original_gains_are_L1_cauchy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T19:22:23.163223+00:00
-- url     : https://prove2.me/submissions/3ff3dccc-3647-4efb-99b4-a97f4e325e66

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_b24_ruincontact_L1_vanish_from_ae_limit_integrable_domination
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (G : ℕ → Ω → ℝ) (M B : Ω → ℝ)
    (hGI : ∀ k, Integrable (G k) P) (hBI : Integrable B P)
    (hDom : ∀ k, ∀ᵐ ω ∂P, ‖G k ω‖ ≤ B ω)
    (hAE : ∀ᵐ ω ∂P, Tendsto (fun k => G k ω) atTop (𝓝 (M ω))) :
    Integrable M P ∧
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ,
        ∀ m l : ℕ, N ≤ m → N ≤ l →
          (∫ ω, ‖G m ω - G l ω‖ ∂P) ≤ ε := by
  have hMMeas : AEStronglyMeasurable M P :=
    aestronglyMeasurable_of_tendsto_ae atTop
      (fun k => (hGI k).aestronglyMeasurable) hAE
  have hMbound : ∀ᵐ ω ∂P, ‖M ω‖ ≤ B ω := by
    filter_upwards [hAE, ae_all_iff.mpr hDom] with ω hω hBω
    exact le_of_tendsto hω.norm (Eventually.of_forall hBω)
  have hMI : Integrable M P :=
    Integrable.mono' hBI hMMeas hMbound
  have hDiffI (k : ℕ) :
      Integrable (fun ω => G k ω - M ω) P :=
    (hGI k).sub hMI
  have hB2I : Integrable (fun ω => 2 * B ω) P :=
    hBI.const_mul 2
  have hDiffDom (k : ℕ) :
      ∀ᵐ ω ∂P, ‖G k ω - M ω‖ ≤ 2 * B ω := by
    filter_upwards [hDom k, hMbound] with ω hGω hMω
    calc
      ‖G k ω - M ω‖ ≤ ‖G k ω‖ + ‖M ω‖ := norm_sub_le _ _
      _ ≤ B ω + B ω := add_le_add hGω hMω
      _ = 2 * B ω := by ring
  have hZero : ∀ᵐ ω ∂P,
      Tendsto (fun k => G k ω - M ω) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [hAE] with ω hω
    have hc : Tendsto (fun _ : ℕ => M ω) atTop (𝓝 (M ω)) :=
      tendsto_const_nhds
    have hsub : Tendsto (fun k => G k ω - M ω) atTop
        (𝓝 (M ω - M ω)) := hω.sub hc
    simpa only [sub_self] using hsub
  have hDCT :=
    AvramDividend.Classical.avram_b24_ruincontact_L1_vanish_from_ae_limit_integrable_domination
      (fun k ω => G k ω - M ω) (fun ω => 2 * B ω)
      hDiffI hB2I hDiffDom hZero
  refine ⟨hMI, ?_⟩
  intro ε hε
  have hHalf : 0 < ε / 2 := by linarith
  have hEvent := hDCT.eventually (Iio_mem_nhds hHalf)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hEvent
  refine ⟨N, ?_⟩
  intro m l hm hl
  have hPath (ω : Ω) :
      ‖G m ω - G l ω‖ ≤
        ‖G m ω - M ω‖ + ‖G l ω - M ω‖ := by
    have heq : G m ω - G l ω =
        (G m ω - M ω) - (G l ω - M ω) := by ring
    rw [heq]
    exact norm_sub_le _ _
  have hPairI : Integrable
      (fun ω => ‖G m ω - M ω‖ + ‖G l ω - M ω‖) P :=
    (hDiffI m).norm.add (hDiffI l).norm
  have hCmp :
      (∫ ω, ‖G m ω - G l ω‖ ∂P) ≤
        (∫ ω, ‖G m ω - M ω‖ +
            ‖G l ω - M ω‖ ∂P) :=
    integral_mono_ae ((hGI m).sub (hGI l)).norm hPairI
      (Filter.Eventually.of_forall hPath)
  calc
    (∫ ω, ‖G m ω - G l ω‖ ∂P) ≤
      (∫ ω, ‖G m ω - M ω‖ +
          ‖G l ω - M ω‖ ∂P) := hCmp
    _ = (∫ ω, ‖G m ω - M ω‖ ∂P) +
        (∫ ω, ‖G l ω - M ω‖ ∂P) := by
      rw [integral_add (hDiffI m).norm (hDiffI l).norm]
    _ ≤ ε := by linarith [hN m hm, hN l hl]
