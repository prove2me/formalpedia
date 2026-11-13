-- Prove2me | solution 1 for AvramDividend.Classical.avram_b29_original_final_stopped_negative_band_count_event_L1_vanish
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T00:06:46.057211+00:00
-- url     : https://prove2.me/submissions/4e4a3357-b777-4295-91c5-1d0c27c70447

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_jump_phys13_original_finite_cutoff_physical_rightcell_count_L1_vanishes
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Actual final stopped negative-band cell counts vanish in every initial-event restricted mean. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (cut : ℕ)
    (τ : Ω → ℝ≥0) (e : ℕ → Ω → ℝ≥0)
    (hτ : Measurable τ) (he : ∀ k, Measurable (e k))
    (heBound : ∀ k ω, e k ω ≤ T)
    (heTendsto : ∀ ω, Tendsto (fun k => e k ω) atTop (𝓝 (τ ω)))
    (A : Set Ω) :
    let B : Set ℝ := Iic (-(1 / ((cut : ℝ) + 1)))
    let J : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let F : ℕ → Ω → ℝ := fun k ω =>
      ((J ω) (Ioc (τ ω) (e k ω) ×ˢ B)).toReal
    (∀ k, Integrable (F k) P) →
    Tendsto (fun k => ∫ ω in A, F k ω ∂P) atTop (𝓝 (0 : ℝ)) := by
  classical
  let B : Set ℝ := Iic (-(1 / ((cut : ℝ) + 1)))
  let J : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  let F : ℕ → Ω → ℝ := fun k ω =>
    ((J ω) (Ioc (τ ω) (e k ω) ×ˢ B)).toReal
  dsimp only
  intro hFint
  have hGlobal : Tendsto (fun k => ∫ ω, F k ω ∂P)
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [F, B, J] using
      (avram_jump_phys13_original_finite_cutoff_physical_rightcell_count_L1_vanishes
        X T cut τ e hτ he heBound heTendsto)
  apply Filter.Tendsto.squeeze
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    hGlobal
  · intro k
    exact integral_nonneg (fun ω => ENNReal.toReal_nonneg)
  · intro k
    exact integral_mono_measure Measure.restrict_le_self
      (Filter.Eventually.of_forall
        (fun ω => ENNReal.toReal_nonneg))
      (hFint k)
