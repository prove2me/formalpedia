-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB157_ae_L2_on_time_interval_from_bounded_double_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T15:46:15.310345+00:00
-- url     : https://prove2.me/submissions/97fc0488-d406-4fd5-b4dc-0df632d9faa8

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB155_bounded_double_ae_L2_iterated_loss_tendsto
import Theorems.Thm_AvramDividend_Classical_avram_gbB156_measurable_set_pointwise_real_sequence_convergence
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (n : ℕ) (hn : 0 < n) (K : ℕ → ℝ → Ω → ℝ) (H : ℝ → Ω → ℝ)
    (hKm : ∀ m, Measurable (fun z : ℝ × Ω => K m z.1 z.2))
    (hHm : Measurable (fun z : ℝ × Ω => H z.1 z.2))
    (BK BH : ℝ) (hBK : 0 ≤ BK) (hBH : 0 ≤ BH)
    (hKb : ∀ m t ω, t ∈ Set.Ioo (0 : ℝ) (n : ℝ) → |K m t ω| ≤ BK)
    (hHb : ∀ t ω, t ∈ Set.Ioo (0 : ℝ) (n : ℝ) → |H t ω| ≤ BH)
    (hae : ∀ᵐ ω ∂P, ∀ᵐ t ∂(volume.restrict (Set.Ioo (0 : ℝ) (n : ℝ))),
      Tendsto (fun m : ℕ => K m t ω) atTop (𝓝 (H t ω))) :
    Tendsto (fun m : ℕ => ∫ t in Set.Ioo (0 : ℝ) (n : ℝ),
      (∫ ω, (K m t ω - H t ω) ^ 2 ∂P) ∂volume)
      atTop (𝓝 (0 : ℝ)) := by
  let I : Set ℝ := Set.Ioo (0 : ℝ) (n : ℝ)
  let μ : Measure ℝ := volume.restrict I
  letI : IsFiniteMeasure μ := inferInstance
  let f : ℕ → ℝ × Ω → ℝ := fun m z =>
    if z.1 ∈ I then K m z.1 z.2 else 0
  let g : ℝ × Ω → ℝ := fun z =>
    if z.1 ∈ I then H z.1 z.2 else 0
  have hmI : MeasurableSet I := measurableSet_Ioo
  have hf : ∀ m, Measurable (f m) := by
    intro m
    exact Measurable.ite (hmI.preimage measurable_fst) (hKm m) measurable_const
  have hg : Measurable g :=
    Measurable.ite (hmI.preimage measurable_fst) hHm measurable_const
  let B : ℝ := max BK BH
  have hB : 0 ≤ B := hBK.trans (le_max_left _ _)
  have hfb : ∀ m z, |f m z| ≤ B := by
    intro m z
    by_cases ht : z.1 ∈ I
    · simpa only [f, if_pos ht] using
        (hKb m z.1 z.2 ht).trans (le_max_left _ _)
    · simp only [f, if_neg ht, abs_zero]
      exact hB
  have hgb : ∀ z, |g z| ≤ B := by
    intro z
    by_cases ht : z.1 ∈ I
    · simpa only [g, if_pos ht] using
        (hHb z.1 z.2 ht).trans (le_max_right _ _)
    · simp only [g, if_neg ht, abs_zero]
      exact hB
  have hEvent : MeasurableSet {z : ℝ × Ω |
      Tendsto (fun m : ℕ => f m z) atTop (𝓝 (g z))} :=
    avram_gbB156_measurable_set_pointwise_real_sequence_convergence
      f g hf hg
  have ha : ∀ᵐ ω ∂P, ∀ᵐ t ∂μ,
      Tendsto (fun m : ℕ => f m (t,ω)) atTop (𝓝 (g (t,ω))) := by
    filter_upwards [hae] with ω hω
    filter_upwards [hω, ae_restrict_mem hmI] with t ht hti
    simpa only [f, g, if_pos hti] using ht
  have hL2 := avram_gbB155_bounded_double_ae_L2_iterated_loss_tendsto
    μ P f g hf hg B hB hfb hgb hEvent ha
  have hEq (m : ℕ) : (∫ t, (∫ ω,
      (K m t ω - H t ω) ^ 2 ∂P) ∂μ) =
      (∫ t, (∫ ω, (f m (t,ω) - g (t,ω)) ^ 2 ∂P) ∂μ) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hmI] with t ht
    simp only [f, g, if_pos ht]
  change Tendsto (fun m : ℕ => ∫ t,
    (∫ ω, (K m t ω - H t ω) ^ 2 ∂P) ∂μ) atTop (𝓝 (0 : ℝ))
  have hfn : (fun m : ℕ => ∫ t,
      (∫ ω, (K m t ω - H t ω) ^ 2 ∂P) ∂μ) =
      (fun m : ℕ => ∫ t,
        (∫ ω, (f m (t,ω) - g (t,ω)) ^ 2 ∂P) ∂μ) := by
    funext m
    exact hEq m
  rw [hfn]
  exact hL2
