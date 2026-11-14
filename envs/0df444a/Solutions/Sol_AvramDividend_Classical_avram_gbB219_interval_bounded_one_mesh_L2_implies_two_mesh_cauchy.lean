-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB219_interval_bounded_one_mesh_L2_implies_two_mesh_cauchy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T07:39:47.729415+00:00
-- url     : https://prove2.me/submissions/b4e8c76b-c44e-4582-a730-6bcea2557e41

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB218_bounded_joint_mesh_L2_limit_implies_nested_pair_cauchy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
noncomputable section
/-- Physical-time bounded nested-L2 one-mesh to two-mesh reduction. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P]
    (n : ℕ) (hn : 0 < n)
    (K : ℕ → ℝ → Ω → ℝ) (H : ℝ → Ω → ℝ)
    (hKm : ∀ m, Measurable (fun z : ℝ × Ω => K m z.1 z.2))
    (hHm : Measurable (fun z : ℝ × Ω => H z.1 z.2))
    (BK BH : ℝ) (hBK : 0 ≤ BK) (hBH : 0 ≤ BH)
    (hKb : ∀ m t ω, t ∈ Set.Ioo (0 : ℝ) (n : ℝ) →
      |K m t ω| ≤ BK)
    (hHb : ∀ t ω, t ∈ Set.Ioo (0 : ℝ) (n : ℝ) →
      |H t ω| ≤ BH)
    (hlim : Tendsto (fun m : ℕ =>
      ∫ t in Set.Ioo (0 : ℝ) (n : ℝ),
        (∫ ω, (K m t ω - H t ω)^2 ∂P) ∂volume)
      atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun mp : ℕ × ℕ =>
      ∫ t in Set.Ioo (0 : ℝ) (n : ℝ),
        (∫ ω, (K mp.1 t ω - K mp.2 t ω)^2 ∂P) ∂volume)
      atTop (𝓝 (0 : ℝ)) := by
  let I : Set ℝ := Ioo (0 : ℝ) (n : ℝ)
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
    · simpa only [f, if_neg ht, abs_zero] using hB
  have hgb : ∀ z, |g z| ≤ B := by
    intro z
    by_cases ht : z.1 ∈ I
    · simpa only [g, if_pos ht] using
        (hHb z.1 z.2 ht).trans (le_max_right _ _)
    · simpa only [g, if_neg ht, abs_zero] using hB
  have hEqOne (m : ℕ) :
      (∫ t, (∫ ω, (f m (t,ω) - g (t,ω))^2 ∂P) ∂μ) =
      (∫ t, (∫ ω, (K m t ω - H t ω)^2 ∂P) ∂μ) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hmI] with t ht
    simp only [f, g, if_pos ht]
  have hlim' : Tendsto (fun m : ℕ =>
      ∫ t, (∫ ω, (f m (t,ω) - g (t,ω))^2 ∂P) ∂μ)
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [hEqOne] using hlim
  have hCauchy :=
    avram_gbB218_bounded_joint_mesh_L2_limit_implies_nested_pair_cauchy
      μ P (fun m t ω => f m (t,ω)) (fun t ω => g (t,ω))
      hf hg B hB (fun m t omega => hfb m (t,omega))
      (fun t omega => hgb (t,omega)) hlim'
  have hEqPair (mp : ℕ × ℕ) :
      (∫ t, (∫ ω,
        (f mp.1 (t,ω) - f mp.2 (t,ω))^2 ∂P) ∂μ) =
      (∫ t, (∫ ω,
        (K mp.1 t ω - K mp.2 t ω)^2 ∂P) ∂μ) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hmI] with t ht
    simp only [f, if_pos ht]
  change Tendsto (fun mp : ℕ × ℕ =>
    ∫ t, (∫ ω,
      (K mp.1 t ω - K mp.2 t ω)^2 ∂P) ∂μ)
    atTop (𝓝 (0 : ℝ))
  simpa only [hEqPair] using hCauchy
