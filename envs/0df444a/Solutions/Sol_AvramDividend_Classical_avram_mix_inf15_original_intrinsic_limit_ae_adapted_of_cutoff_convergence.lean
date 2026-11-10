-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_inf15_original_intrinsic_limit_ae_adapted_of_cutoff_convergence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T12:58:56.849401+00:00
-- url     : https://prove2.me/submissions/4a8e56a7-789a-427b-b1ce-3c3ca858f5a7

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hCut : ∀ (n : ℕ) (T : ℝ≥0),
      Measurable[𝓕.rightCont T]
        (fun ω : Ω => avram_p4_h_gaussian_intrinsic_truncated_residual X n T ω))
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      Tendsto
        (fun n : ℕ => avram_p4_h_gaussian_intrinsic_truncated_residual X n T ω)
        atTop (nhds (R T ω))) :
    ∀ T : ℝ≥0, AEStronglyMeasurable[𝓕.rightCont T] (R T) P := by
  classical
  intro T
  let f : ℕ → Ω → ℝ := fun n ω =>
    avram_p4_h_gaussian_intrinsic_truncated_residual X n T ω
  let E : Set Ω := {ω | ∃ l : ℝ, Tendsto (fun n => f n ω) atTop (nhds l)}
  have hE : MeasurableSet[𝓕.rightCont T] E := by
    letI : MeasurableSpace Ω := 𝓕.rightCont T
    exact MeasureTheory.measurableSet_exists_tendsto
      (fun n => hCut n T)
  let f' : ℕ → Ω → ℝ := fun n ω => if ω ∈ E then f n ω else 0
  have hF' : ∀ n : ℕ, Measurable[𝓕.rightCont T] (f' n) := by
    intro n
    letI : MeasurableSpace Ω := 𝓕.rightCont T
    exact Measurable.ite
      (f := f n) (g := fun _ : Ω => (0 : ℝ))
      (p := fun ω => ω ∈ E) hE (hCut n T) measurable_const
  have hAll : ∀ ω : Ω, ∃ l : ℝ,
      Tendsto (fun n => f' n ω) atTop (nhds l) := by
    intro ω
    by_cases hw : ω ∈ E
    · change (∃ l : ℝ, Tendsto (fun n => f n ω) atTop (nhds l)) at hw
      rcases hw with ⟨l, hl⟩
      have hwE : ω ∈ E := ⟨l, hl⟩
      exact ⟨l, by simpa [f', hwE] using hl⟩
    · refine ⟨0, ?_⟩
      simpa [f', hw] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
  let g : Ω → ℝ := fun ω => Classical.choose (hAll ω)
  have hgLim (ω : Ω) :
      Tendsto (fun n => f' n ω) atTop (nhds (g ω)) :=
    Classical.choose_spec (hAll ω)
  have hgMeas : Measurable[𝓕.rightCont T] g := by
    letI : MeasurableSpace Ω := 𝓕.rightCont T
    exact measurable_of_tendsto_metrizable
      (f := f') (g := g) hF' (tendsto_pi_nhds.mpr hgLim)
  have hEq : ∀ᵐ ω ∂P, g ω = R T ω := by
    filter_upwards [hR] with ω hω
    have hw : ω ∈ E := ⟨R T ω, hω T⟩
    have hg : Tendsto (fun n => f n ω) atTop (nhds (g ω)) := by
      simpa [f', hw] using hgLim ω
    exact tendsto_nhds_unique hg (hω T)
  have hgAE : AEStronglyMeasurable[𝓕.rightCont T] g P :=
    hgMeas.aestronglyMeasurable
  exact hgAE.congr hEq
