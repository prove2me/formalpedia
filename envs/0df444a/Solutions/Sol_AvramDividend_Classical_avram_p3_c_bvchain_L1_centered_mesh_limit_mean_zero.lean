-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_c_bvchain_L1_centered_mesh_limit_mean_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T09:44:23.755848+00:00
-- url     : https://prove2.me/submissions/d1101aad-ef65-43e0-abfe-0386012439bf

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_L1_mesh_residual_mean_nonpos
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter AvramDividend.Classical

/-- A centered sequence converging in L1 has an exactly centered limit. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (R : Ω → ℝ) (Rmesh : ℕ → Ω → ℝ)
    (hR : Integrable R P)
    (hMesh : ∀ n, Integrable (Rmesh n) P)
    (hMean : ∀ n, (∫ ω, Rmesh n ω ∂P) = 0)
    (hError : Tendsto (fun n => (∫ ω, |Rmesh n ω - R ω| ∂P))
      atTop (nhds (0 : ℝ))) :
    (∫ ω, R ω ∂P) = 0 := by
  have hle : (∫ ω, R ω ∂P) ≤ 0 :=
    avram_p3_c_bvchain_L1_mesh_residual_mean_nonpos
      P R Rmesh hR hMesh (fun n => (hMean n).le) hError
  have hNegError :
      Tendsto (fun n => (∫ ω, |(-Rmesh n ω) - (-R ω)| ∂P))
        atTop (nhds (0 : ℝ)) := by
    simpa only [neg_sub_neg, abs_sub_comm] using hError
  have hNegMean (n : ℕ) :
      (∫ ω, -Rmesh n ω ∂P) ≤ 0 := by
    simpa only [integral_neg, hMean n, neg_zero] using (le_refl (0 : ℝ))
  have hneg :
      (∫ ω, -R ω ∂P) ≤ 0 :=
    avram_p3_c_bvchain_L1_mesh_residual_mean_nonpos
      P (fun ω => -R ω) (fun n ω => -Rmesh n ω)
      hR.neg (fun n => (hMesh n).neg) hNegMean hNegError
  have hge : 0 ≤ (∫ ω, R ω ∂P) := by
    have h : -(∫ ω, R ω ∂P) ≤ 0 := by
      simpa only [integral_neg] using hneg
    exact neg_nonpos.mp h
  exact le_antisymm hle hge
