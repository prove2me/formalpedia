-- Prove2me | solution 1 for AvramDividend.Classical.avram_jb23_dominated_two_channel_initial_centering_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T22:11:10.332993+00:00
-- url     : https://prove2.me/submissions/c1b5b758-b688-4338-910e-21021a3740db

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ja18_original_dominated_condExp_zero_limit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Integrable dominated limits retain initial conditional centring in each noise channel. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (G J : ℕ → Ω → ℝ) (MG MJ BG BJ : Ω → ℝ)
    (hGI : ∀ k, Integrable (G k) P)
    (hJI : ∀ k, Integrable (J k) P)
    (hGconv : ∀ᵐ ω ∂P, Tendsto (fun k => G k ω) atTop (𝓝 (MG ω)))
    (hJconv : ∀ᵐ ω ∂P, Tendsto (fun k => J k ω) atTop (𝓝 (MJ ω)))
    (hBG : Integrable BG P) (hBJ : Integrable BJ P)
    (hGdom : ∀ k, ∀ᵐ ω ∂P, ‖G k ω‖ ≤ BG ω)
    (hJdom : ∀ k, ∀ᵐ ω ∂P, ‖J k ω‖ ≤ BJ ω)
    (hGzero : ∀ k, P[G k | 𝓕.rightCont 0] =ᵐ[P] (fun _ => (0 : ℝ)))
    (hJzero : ∀ k, P[J k | 𝓕.rightCont 0] =ᵐ[P] (fun _ => (0 : ℝ))) :
    Integrable MG P ∧
    (P[MG | 𝓕.rightCont 0] =ᵐ[P] (fun _ => (0 : ℝ))) ∧
    Integrable MJ P ∧
    (P[MJ | 𝓕.rightCont 0] =ᵐ[P] (fun _ => (0 : ℝ))) := by
  have hGAE : AEStronglyMeasurable MG P :=
    aestronglyMeasurable_of_tendsto_ae atTop
      (fun k => (hGI k).aestronglyMeasurable) hGconv
  have hJAE : AEStronglyMeasurable MJ P :=
    aestronglyMeasurable_of_tendsto_ae atTop
      (fun k => (hJI k).aestronglyMeasurable) hJconv
  have hGb : ∀ᵐ ω ∂P, ‖MG ω‖ ≤ ‖BG ω‖ := by
    have hd : ∀ᵐ ω ∂P, ∀ k, ‖G k ω‖ ≤ BG ω :=
      ae_all_iff.mpr hGdom
    filter_upwards [hGconv, hd] with ω hc hb
    have hh := le_of_tendsto hc.norm (Filter.Eventually.of_forall hb)
    exact hh.trans (by simpa only [Real.norm_eq_abs] using
      (le_abs_self (BG ω)))
  have hJb : ∀ᵐ ω ∂P, ‖MJ ω‖ ≤ ‖BJ ω‖ := by
    have hd : ∀ᵐ ω ∂P, ∀ k, ‖J k ω‖ ≤ BJ ω :=
      ae_all_iff.mpr hJdom
    filter_upwards [hJconv, hd] with ω hc hb
    have hh := le_of_tendsto hc.norm (Filter.Eventually.of_forall hb)
    exact hh.trans (by simpa only [Real.norm_eq_abs] using
      (le_abs_self (BJ ω)))
  refine ⟨hBG.mono hGAE hGb, ?_, hBJ.mono hJAE hJb, ?_⟩
  · exact avram_ja18_original_dominated_condExp_zero_limit
      G MG BG hGI hGconv hBG hGdom hGzero
  · exact avram_ja18_original_dominated_condExp_zero_limit
      J MJ BJ hJI hJconv hBJ hJdom hJzero
