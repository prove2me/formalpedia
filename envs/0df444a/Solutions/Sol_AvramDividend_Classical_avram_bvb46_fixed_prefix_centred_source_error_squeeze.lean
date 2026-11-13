-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb46_fixed_prefix_centred_source_error_squeeze
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T20:52:15.167435+00:00
-- url     : https://prove2.me/submissions/99e40b50-984a-4a92-8158-55846ac69773

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter
open scoped Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (F B M : ℕ → Ω → ℝ) (a : ℝ)
    (hFI : ∀ n, Integrable (F n) P)
    (hMI : ∀ n, Integrable (M n) P)
    (hEI : ∀ k, Integrable
      (fun ω => max (F k ω - (a + (M k ω + B k ω))) (0 : ℝ)) P)
    (hFmono : ∀ᵐ ω ∂P, ∀ n k, n ≤ k → F n ω ≤ F k ω)
    (hBnonpos : ∀ᵐ ω ∂P, ∀ k, B k ω ≤ 0)
    (hErr : Tendsto (fun k =>
       ∫ ω, max (F k ω - (a + (M k ω + B k ω))) (0 : ℝ) ∂P)
       atTop (𝓝 (0 : ℝ))) :
    ∀ n, Tendsto (fun k =>
       ∫ ω, max (F n ω - (a + M k ω)) (0 : ℝ) ∂P)
       atTop (𝓝 (0 : ℝ)) := by
  intro n
  have hOrd (k : ℕ) (hk : n ≤ k) : ∀ᵐ ω ∂P,
      max (F n ω - (a + M k ω)) (0 : ℝ) ≤
      max (F k ω - (a + (M k ω + B k ω))) (0 : ℝ) := by
    filter_upwards [hFmono, hBnonpos] with ω hf hb
    apply max_le_max _ le_rfl
    linarith [hf n k hk, hb k]
  have hLI (k : ℕ) (hk : n ≤ k) : Integrable
      (fun ω => max (F n ω - (a + M k ω)) (0 : ℝ)) P := by
    have hSub : AEStronglyMeasurable
        (fun ω => F n ω - (a + M k ω)) P := by
      exact (hFI n).aestronglyMeasurable.sub
        (aestronglyMeasurable_const.add (hMI k).aestronglyMeasurable)
    have hMax : AEStronglyMeasurable
        (fun ω => max (F n ω - (a + M k ω)) (0 : ℝ)) P := by
      exact hSub.sup aestronglyMeasurable_const
    exact (hEI k).mono_nonneg hMax
      (Filter.Eventually.of_forall (fun ω => le_max_right _ _))
      (hOrd k hk)
  have hLnonneg : ∀ k : ℕ,
      0 ≤ ∫ ω, max (F n ω - (a + M k ω)) (0 : ℝ) ∂P := by
    intro k
    exact integral_nonneg (fun ω => le_max_right _ _)
  have hAbove : ∀ᶠ k : ℕ in atTop,
      (∫ ω, max (F n ω - (a + M k ω)) (0 : ℝ) ∂P) ≤
      (∫ ω, max (F k ω - (a + (M k ω + B k ω)))
            (0 : ℝ) ∂P) := by
    filter_upwards [eventually_ge_atTop n] with k hk
    exact integral_mono_ae (hLI k hk) (hEI k) (hOrd k hk)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    hErr
  · exact Filter.Eventually.of_forall hLnonneg
  · exact hAbove
