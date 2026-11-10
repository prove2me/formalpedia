-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_reward14_original_finite_cutoff_stopped_weighted_rightcell_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T11:18:01.826289+00:00
-- url     : https://prove2.me/submissions/6857a74f-9a6e-4005-a6b2-d855ab8b3493

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_jump_phys13_original_finite_cutoff_physical_rightcell_count_L1_vanishes
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Transfer original stopped finite-cutoff jump count L1 convergence to a dominated weighted source error. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (cut : ℕ)
    (τ : Ω → ℝ≥0) (e : ℕ → Ω → ℝ≥0)
    (hτ : Measurable τ) (he : ∀ k, Measurable (e k))
    (heBound : ∀ k ω, e k ω ≤ T)
    (heTendsto : ∀ ω, Tendsto (fun k => e k ω) atTop (𝓝 (τ ω))) :
    let B : Set ℝ := Iic (-(1 / ((cut : ℝ) + 1)))
    let J : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let N : ℕ → Ω → ℝ := fun k ω =>
      ((J ω) (Ioc (τ ω) (e k ω) ×ˢ B)).toReal
    ∀ (F : ℕ → Ω → ℝ) (K : ℝ),
      0 ≤ K →
      (∀ k, Integrable (F k) P) →
      (∀ k, Integrable (N k) P) →
      (∀ k ω, |F k ω| ≤ K * N k ω) →
      Tendsto (fun k => ∫ ω, |F k ω| ∂P) atTop (𝓝 (0 : ℝ)) := by
  dsimp only
  intro F K hK hFI hNI hBound
  let B : Set ℝ := Iic (-(1 / ((cut : ℝ) + 1)))
  let J : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  let N : ℕ → Ω → ℝ := fun k ω =>
    ((J ω) (Ioc (τ ω) (e k ω) ×ˢ B)).toReal
  have hc : Tendsto (fun k => ∫ ω, N k ω ∂P) atTop (𝓝 (0 : ℝ)) := by
    simpa only [N, J, B] using
      (avram_jump_phys13_original_finite_cutoff_physical_rightcell_count_L1_vanishes
        X T cut τ e hτ he heBound heTendsto)
  have hlo (k : ℕ) : (0 : ℝ) ≤ ∫ ω, |F k ω| ∂P := by
    exact integral_nonneg (fun ω => abs_nonneg (F k ω))
  have hhi (k : ℕ) :
      (∫ ω, |F k ω| ∂P) ≤ K * (∫ ω, N k ω ∂P) := by
    calc
      (∫ ω, |F k ω| ∂P) ≤ ∫ ω, K * N k ω ∂P := by
        exact integral_mono (hFI k).abs ((hNI k).const_mul K) (hBound k)
      _ = K * (∫ ω, N k ω ∂P) := integral_const_mul K (N k)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    (by simpa using (Filter.Tendsto.const_mul K hc))
    hlo hhi
