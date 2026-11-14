-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB215_generic_physical_clipped_mesh_measurable_bounded
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T07:25:30.886483+00:00
-- url     : https://prove2.me/submissions/7e870bb9-9398-40e7-908c-bee8e314dc7e

import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Analysis.Calculus.Deriv.Basic
import Theorems.Thm_AvramDividend_Classical_avram_gbB209_generic_stopped_clipped_NNReal_mesh_joint_measurable
import Theorems.Thm_AvramDividend_Classical_avram_gbB214_real_time_stopped_clipped_joint_measurable
import Theorems.Thm_AvramDividend_Classical_avram_gbB211_continuous_gradient_compact_clip_Borel_measurable
import Theorems.Thm_AvramDividend_Classical_avram_gbB213_generic_stopped_clipped_NNReal_uniform_grid_amplitude
import Theorems.Thm_AvramDividend_Classical_avram_gbB212_stopped_discounted_compact_clip_uniform_amplitude
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Real-time clipped physical mesh measurability and bounds. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (Y : ℝ≥0 → Ω → ℝ)
    (hY : Measurable (fun z : ℝ≥0 × Ω => Y z.1 z.2))
    (ρ : Ω → ℝ≥0) (hρ : Measurable ρ)
    (w : ℝ → ℝ) (a b : ℝ)
    (hc : ContinuousOn (deriv w) (Icc a b))
    (q : ℝ) (hq : 0 ≤ q) (n : ℕ) (hn : 0 < n) :
    let G : ℕ → ℕ → Ω → ℝ := fun m i ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
      let s : ℝ≥0 := (i : ℝ≥0) * Δ
      if s < ρ ω then Real.exp (-(q * (s : ℝ))) *
        (if Y s ω ∈ Icc a b then deriv w (Y s ω) else 1)
      else 0
    let K : ℕ → ℝ → Ω → ℝ := fun m t ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
      (Finset.range (m + 1)).sum (fun i =>
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        if (s : ℝ) ≤ t ∧ t < ((s + Δ : ℝ≥0) : ℝ)
        then G m i ω else 0)
    let H : ℝ → Ω → ℝ := fun t ω =>
      if t < (ρ ω : ℝ) then
        Real.exp (-(q * t)) *
          (if Y (Real.toNNReal t) ω ∈ Icc a b
            then deriv w (Y (Real.toNNReal t) ω) else 1)
      else 0
    (∀ m, Measurable (fun z : ℝ × Ω => K m z.1 z.2)) ∧
    Measurable (fun z : ℝ × Ω => H z.1 z.2) ∧
    ∃ B : ℝ, 0 ≤ B ∧
      (∀ m t ω, t ∈ Ioo (0 : ℝ) (n : ℝ) → |K m t ω| ≤ B) ∧
      (∀ t ω, t ∈ Ioo (0 : ℝ) (n : ℝ) → |H t ω| ≤ B) := by
  intro G K H
  let g : ℝ → ℝ := fun y =>
    if y ∈ Icc a b then deriv w y else 1
  have hg : Measurable g :=
    avram_gbB211_continuous_gradient_compact_clip_Borel_measurable
      w a b hc
  have hMeas :=
    avram_gbB209_generic_stopped_clipped_NNReal_mesh_joint_measurable
      Y hY ρ hρ g hg q n
  have hK : ∀ m, Measurable (fun z : ℝ × Ω => K m z.1 z.2) := by
    simpa only [K, G, g] using hMeas.1
  have hH : Measurable (fun z : ℝ × Ω => H z.1 z.2) := by
    have hm :=
      avram_gbB214_real_time_stopped_clipped_joint_measurable
        Y hY ρ hρ g hg q
    simpa only [H, g] using hm
  obtain ⟨BK, hBK, hKBound⟩ :=
    avram_gbB213_generic_stopped_clipped_NNReal_uniform_grid_amplitude
      Y ρ w a b hc q hq n hn
  obtain ⟨BH, hBH, hHBound⟩ :=
    avram_gbB212_stopped_discounted_compact_clip_uniform_amplitude
      w a b hc q hq Y ρ
  refine ⟨hK, hH, max BK BH, le_trans hBK (le_max_left _ _), ?_, ?_⟩
  · intro m t ω ht
    exact le_trans (hKBound m t ω ht) (le_max_left _ _)
  · intro t ω ht
    have hco : (Real.toNNReal t : ℝ) = t :=
      Real.coe_toNNReal _ (le_of_lt ht.1)
    have hLt : (Real.toNNReal t < ρ ω) ↔
        t < (ρ ω : ℝ) := by
      constructor
      · intro hs
        have hh : (Real.toNNReal t : ℝ) < (ρ ω : ℝ) := by
          exact_mod_cast hs
        simpa only [hco] using hh
      · intro hs
        have hh : (Real.toNNReal t : ℝ) < (ρ ω : ℝ) := by
          simpa only [hco] using hs
        exact_mod_cast hh
    have hAt := hHBound (Real.toNNReal t) ω
    have hAt' : |H t ω| ≤ BH := by
      simpa only [H, hco, hLt] using hAt
    exact le_trans hAt' (le_max_right _ _)

