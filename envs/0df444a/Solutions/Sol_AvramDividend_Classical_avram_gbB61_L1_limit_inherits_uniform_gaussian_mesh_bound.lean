-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB61_L1_limit_inherits_uniform_gaussian_mesh_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T16:51:50.228464+00:00
-- url     : https://prove2.me/submissions/ff88d45a-9b1f-4459-af1f-22d261309026

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB54y_positive_excess_L1_and_approximation_L1_imply_ae_upper
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter AvramDividend.Classical
open scoped ENNReal Topology
noncomputable section
/-- An L1 limit inherits every deterministic uniform bound on its mesh approximations. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (N : Ω → ℝ) (M : ℕ → Ω → ℝ)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hNI : Integrable N μ) (hMI : ∀ m, Integrable (M m) μ)
    (hBound : ∀ m ω, |M m ω| ≤ ε)
    (hL1 : Tendsto (fun m => ∫ ω, |N ω - M m ω| ∂μ)
      atTop (𝓝 (0 : ℝ))) :
    ∀ᵐ ω ∂μ, |N ω| ≤ ε := by
  have hConst : Integrable (fun _ : Ω => -ε) μ := integrable_const _
  have hLowZero (m : ℕ) :
      (∫ ω, max (-ε - M m ω) 0 ∂μ) = 0 := by
    have hh : (fun ω : Ω => max (-ε - M m ω) 0) =
        (fun _ => (0 : ℝ)) := by
      funext ω
      have hlo := (abs_le.mp (hBound m ω)).1
      exact max_eq_right (by linarith)
    rw [hh]
    simp
  have hLowRes : Tendsto (fun m : ℕ =>
      ∫ ω, max (-ε - M m ω) 0 ∂μ) atTop (𝓝 (0 : ℝ)) := by
    simp only [hLowZero]
    exact tendsto_const_nhds
  have hlo :=
    avram_gbB54y_positive_excess_L1_and_approximation_L1_imply_ae_upper
      μ (fun _ => -ε) N M hConst hNI hMI hLowRes hL1
  have hHighZero (m : ℕ) :
      (∫ ω, max (-ε - -M m ω) 0 ∂μ) = 0 := by
    have hh : (fun ω : Ω => max (-ε - -M m ω) 0) =
        (fun _ => (0 : ℝ)) := by
      funext ω
      have hhi := (abs_le.mp (hBound m ω)).2
      exact max_eq_right (by linarith)
    rw [hh]
    simp
  have hHighRes : Tendsto (fun m : ℕ =>
      ∫ ω, max (-ε - -M m ω) 0 ∂μ) atTop (𝓝 (0 : ℝ)) := by
    simp only [hHighZero]
    exact tendsto_const_nhds
  have hDiff : Tendsto (fun m : ℕ =>
      ∫ ω, |(-N ω) - (-M m ω)| ∂μ) atTop (𝓝 (0 : ℝ)) := by
    convert hL1 using 1
    ext m
    congr 1
    ext ω
    rw [show -N ω - -M m ω = -(N ω - M m ω) by ring, abs_neg]
  have hhi :=
    avram_gbB54y_positive_excess_L1_and_approximation_L1_imply_ae_upper
      μ (fun _ => -ε) (fun ω => -N ω) (fun m ω => -M m ω)
      hConst hNI.neg (fun m => (hMI m).neg) hHighRes hDiff
  filter_upwards [hlo, hhi] with ω hlow hhigh
  exact abs_le.mpr ⟨hlow, by linarith⟩
